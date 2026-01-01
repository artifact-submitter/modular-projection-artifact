#!/usr/bin/env python3
"""Run and verify the complete fresh-project CertifiedJL release validation.

The release lane deliberately reuses only exact, clean dependency checkouts.  It
copies the tracked project into an isolated workspace whose project build
directory has never existed, builds every production module explicitly, checks
the complete project artifact set, compiles the generated reviewer entry point,
and asks ``leanchecker --fresh`` to replay one generated all-production module
with one Lean worker thread.

Computing an input identity is not execution evidence.  Only a sealed receipt
with ``success: true`` produced after every required step has completed attests
release validation, and its build scope is always described as a fresh *project*
build with preverified dependency artifacts.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
from typing import Any, Iterable, Mapping, Sequence

from native_shadow_replay import NativeReplayError, verified_dependencies
from reviewer_workspace import entries as reviewer_entries


ROOT = Path(__file__).resolve().parent.parent
SCHEMA_VERSION = 1
RECORD_KIND = "release-validation-receipt"
IDENTITY_KIND = "release-inputs"
GENERATED_MODULE = "CertifiedJLReleaseAll"
RECEIPT_NAME = "release-validation-receipt.json"
FAILURE_NAME = "release-validation-failure.json"
SOURCE_MANIFEST_NAME = "release-source-manifest.json"
PACKAGE_SOURCE_MANIFEST_NAME = ".lake/release-package-source-manifest.json"
HASH = re.compile(r"sha256:[0-9a-f]{64}")
CONFIGURATION_INPUTS = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
)
PROCEDURE_AUTHORITIES = (
    "evidence/result-catalog.toml",
    "evidence/theorem-contract.toml",
)
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")


class ReleaseValidationError(ValueError):
    """A release-validation precondition or execution step failed."""

    def __init__(self, message: str, *, step: dict[str, object] | None = None):
        super().__init__(message)
        self.step = step


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )


def canonical_digest(domain: str, value: object) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(domain.encode("utf-8") + b"\0" + payload).hexdigest()


def sha256_bytes(value: bytes) -> str:
    return "sha256:" + hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return "sha256:" + digest.hexdigest()


def _git(root: Path, *arguments: str) -> bytes:
    return subprocess.check_output(["git", *arguments], cwd=root)


def _frozen_manifest_digest(document: Mapping[str, object]) -> str:
    return canonical_digest(
        "CertifiedJL-release-source-manifest-v1",
        {key: value for key, value in document.items() if key != "manifest_digest"},
    )


def write_frozen_source_manifest(
    root: Path, paths: Iterable[Path], output: Path,
) -> dict[str, object]:
    records = _inventory(root, paths)
    document: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": "release-source-manifest",
        "files": records,
    }
    document["manifest_digest"] = _frozen_manifest_digest(document)
    _write_json_new(output, document)
    return document


def _read_frozen_source_manifest(root: Path, path: Path) -> tuple[Path, ...]:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReleaseValidationError(f"cannot read frozen source manifest: {error}") from error
    if (
        not isinstance(document, dict)
        or set(document) != {"schema_version", "record_kind", "files", "manifest_digest"}
        or document["schema_version"] != SCHEMA_VERSION
        or document["record_kind"] != "release-source-manifest"
        or document["manifest_digest"] != _frozen_manifest_digest(document)
    ):
        raise ReleaseValidationError("invalid frozen release source manifest")
    _validate_inventory(document["files"], "frozen_source_manifest.files")
    result = []
    for record in document["files"]:
        candidate = root / record["path"]
        if (
            candidate.is_symlink() or not candidate.is_file()
            or candidate.stat().st_size != record["size_bytes"]
            or sha256_file(candidate) != record["sha256"]
        ):
            raise ReleaseValidationError(
                f"frozen source manifest input differs: {record['path']}"
            )
        result.append(candidate)
    # Fail closed on every injected source-tree entry.  Build/dependency state is
    # separately attested and the manifest necessarily describes itself only by
    # its sealed payload.
    known = {path.resolve() for path in result}
    for candidate in root.rglob("*"):
        relative = candidate.relative_to(root)
        if relative.parts[:1] == (".lake",) or relative.as_posix() == SOURCE_MANIFEST_NAME:
            continue
        if candidate.is_symlink() or (candidate.is_file() and candidate.resolve() not in known):
            raise ReleaseValidationError(
                f"source is absent from frozen release manifest: {relative}"
            )
    return tuple(result)


def tracked_files(root: Path = ROOT) -> tuple[Path, ...]:
    """Return every tracked path, rejecting absent and symlinked inputs."""
    if not (root / ".git").exists():
        manifest = root / SOURCE_MANIFEST_NAME
        if manifest.is_file():
            return _read_frozen_source_manifest(root, manifest)
        raise ReleaseValidationError(
            f"release validation requires Git or {SOURCE_MANIFEST_NAME}"
        )
    try:
        payload = _git(root, "ls-files", "-z")
    except (OSError, subprocess.CalledProcessError) as error:
        manifest = root / SOURCE_MANIFEST_NAME
        if manifest.is_file():
            return _read_frozen_source_manifest(root, manifest)
        raise ReleaseValidationError(
            f"release validation requires Git or {SOURCE_MANIFEST_NAME}"
        ) from error
    result = tuple(root / os.fsdecode(name) for name in payload.split(b"\0") if name)
    if not result:
        raise ReleaseValidationError("release validation found no tracked files")
    for path in result:
        if path.is_symlink() or not path.is_file():
            raise ReleaseValidationError(
                f"tracked release input must be a regular file: {path.relative_to(root)}"
            )
    return result


def require_clean_checkout(root: Path = ROOT) -> str:
    status = _git(root, "status", "--porcelain=v1", "--untracked-files=all")
    if status:
        raise ReleaseValidationError(
            "release validation requires a clean checkout; untracked files also invalidate it"
        )
    commit = _git(root, "rev-parse", "HEAD").decode("ascii").strip()
    if re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", commit) is None:
        raise ReleaseValidationError("release validation could not resolve the source commit")
    return commit


def lean_source_class(relative: Path) -> str:
    """Classify one tracked Lean source into one and only one release class."""
    parts = relative.parts
    value = relative.as_posix()
    if relative.suffix != ".lean":
        raise ReleaseValidationError(f"not a Lean source: {value}")
    if parts[:2] in (("CertifiedJL", "Tests"), ("CertifiedJLFast", "Tests")):
        return "tests"
    if value == "CertifiedJLFast.lean" or parts[:1] == ("CertifiedJLFast",):
        return "certifiedjl_fast"
    if value == "CertifiedJL.lean" or parts[:1] == ("CertifiedJL",):
        return "production_certifiedjl"
    if parts[:1] == ("Vendor",):
        return "production_vendor"
    if parts[:1] == ("scripts",):
        return "scripts"
    raise ReleaseValidationError(f"unclassified tracked Lean source: {value}")


def classify_lean_sources(
    root: Path = ROOT, paths: Iterable[Path] | None = None,
) -> dict[str, tuple[Path, ...]]:
    classes: dict[str, list[Path]] = {
        "production_certifiedjl": [],
        "production_vendor": [],
        "tests": [],
        "certifiedjl_fast": [],
        "scripts": [],
    }
    selected = tracked_files(root) if paths is None else tuple(paths)
    lean = sorted(path for path in selected if path.suffix == ".lean")
    for path in lean:
        try:
            relative = path.relative_to(root)
        except ValueError as error:
            raise ReleaseValidationError(f"Lean source is outside checkout: {path}") from error
        classes[lean_source_class(relative)].append(path)
    if not lean:
        raise ReleaseValidationError("release validation found no tracked Lean sources")
    if not classes["production_certifiedjl"] or not classes["production_vendor"]:
        raise ReleaseValidationError("release validation production source classes are incomplete")
    return {name: tuple(values) for name, values in classes.items()}


def module_name(root: Path, source: Path) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def _inventory(root: Path, paths: Iterable[Path]) -> list[dict[str, object]]:
    answer = []
    for path in sorted(set(paths)):
        if path.is_symlink() or not path.is_file():
            raise ReleaseValidationError(
                f"release identity input must be a regular file: {path.relative_to(root)}"
            )
        answer.append({
            "path": path.relative_to(root).as_posix(),
            "size_bytes": path.stat().st_size,
            "sha256": sha256_file(path),
        })
    answer.sort(key=lambda record: str(record["path"]))
    return answer


def _manifest_dependencies(root: Path) -> list[dict[str, object]]:
    try:
        manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReleaseValidationError(f"cannot read lake-manifest.json: {error}") from error
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise ReleaseValidationError("lake-manifest.json has no package list")
    result = []
    for package in packages:
        if not isinstance(package, dict):
            raise ReleaseValidationError("lake-manifest.json has an invalid package entry")
        selected = {
            key: package.get(key)
            for key in ("name", "type", "scope", "url", "rev", "subDir")
        }
        if (
            not isinstance(selected["name"], str)
            or selected["type"] != "git"
            or not isinstance(selected["url"], str)
            or re.fullmatch(r"[0-9a-f]{40}", str(selected["rev"])) is None
            or selected["subDir"] is not None
        ):
            raise ReleaseValidationError(
                f"unsupported or inexact dependency manifest entry: {selected!r}"
            )
        result.append(selected)
    names = [str(record["name"]) for record in result]
    if len(names) != len(set(names)):
        raise ReleaseValidationError("lake-manifest.json has duplicate package names")
    return sorted(result, key=lambda record: str(record["name"]))


def _reviewer_target_projection(root: Path) -> list[dict[str, str]]:
    """Bind the audit targets while excluding paper locators and prose."""
    return sorted(
        ({key: row[key] for key in ("id", "declaration", "source")}
         for row in reviewer_entries(root)),
        key=lambda row: (row["id"], row["declaration"], row["source"]),
    )


def proof_identity_projection(identity: Mapping[str, object]) -> dict[str, object]:
    required = {
        "proof_closure_digest", "proof_inputs", "dependencies", "production_modules",
    }
    if not required <= set(identity):
        raise ValueError("release identity has no complete proof projection")
    return {
        "schema_version": SCHEMA_VERSION,
        "identity_kind": "proof-bundle-inputs",
        "proof_closure_digest": identity["proof_closure_digest"],
        "proof_inputs": identity["proof_inputs"],
        "dependencies": identity["dependencies"],
        "production_modules": identity["production_modules"],
    }


def compute_release_identity(root: Path = ROOT) -> dict[str, object]:
    """Compute the checkout-independent input identity for release validation.

    Paper and documentation bytes are deliberately absent.  The proof identity
    contains production Lean/config/dependency inputs.  The distinct procedure
    identity contains tracked validator scripts plus the semantic reviewer
    target projection, not paper locators stored beside those targets.
    """
    root = root.resolve()
    tracked = tracked_files(root)
    classes = classify_lean_sources(root, tracked)
    production = (*classes["production_certifiedjl"], *classes["production_vendor"])
    lean_classification = _classification_document(root, classes)
    configuration = []
    for relative in CONFIGURATION_INPUTS:
        path = root / relative
        if path not in tracked:
            raise ReleaseValidationError(f"untracked release configuration: {relative}")
        configuration.append(path)
    procedure = [
        path for path in tracked
        if path.relative_to(root).parts[:1] == ("scripts",)
    ]
    for relative in PROCEDURE_AUTHORITIES:
        if root / relative not in tracked:
            raise ReleaseValidationError(f"untracked reviewer authority: {relative}")

    certificate_inputs = [
        path for path in tracked
        if path.relative_to(root).parts[:2] == ("evidence", "certificates")
    ]
    validation_roots = root / "evidence/validation-roots.toml"
    if validation_roots not in tracked:
        raise ReleaseValidationError("untracked release proof authority: evidence/validation-roots.toml")
    proof_inputs = _inventory(
        root, (*production, *configuration, *certificate_inputs, validation_roots)
    )
    dependencies = _manifest_dependencies(root)
    production_modules = sorted(module_name(root, path) for path in production)
    proof_digest = canonical_digest("CertifiedJL-release-proof-closure-v1", {
        "inputs": proof_inputs,
        "dependencies": dependencies,
        "production_modules": production_modules,
    })
    procedure_inputs = _inventory(root, procedure)
    reviewer_targets = _reviewer_target_projection(root)
    procedure_digest = canonical_digest("CertifiedJL-release-procedure-v1", {
        "inputs": procedure_inputs,
        "reviewer_targets": reviewer_targets,
        "lean_source_classification_digest": lean_classification["digest"],
        "standard_axioms": list(STANDARD_AXIOMS),
        "all_production_module": GENERATED_MODULE,
        "leanchecker": {"fresh": True, "lean_num_threads": "1"},
    })
    validation_digest = canonical_digest("CertifiedJL-release-validation-inputs-v1", {
        "proof_closure_digest": proof_digest,
        "validation_procedure_digest": procedure_digest,
    })
    return {
        "schema_version": SCHEMA_VERSION,
        "identity_kind": IDENTITY_KIND,
        "mode": "release",
        "proof_closure_digest": proof_digest,
        "validation_procedure_digest": procedure_digest,
        "validation_digest": validation_digest,
        "digest": validation_digest,
        "proof_inputs": proof_inputs,
        "procedure_inputs": procedure_inputs,
        "dependencies": dependencies,
        "production_modules": production_modules,
        "reviewer_targets": reviewer_targets,
        "lean_source_classification": lean_classification,
        "paper_and_docs_excluded": True,
    }


def _classification_document(
    root: Path, classes: Mapping[str, Sequence[Path]],
) -> dict[str, object]:
    inventories = {name: _inventory(root, paths) for name, paths in classes.items()}
    result: dict[str, object] = {
        "all_tracked_lean_sources_classified": True,
        "categories": inventories,
        "counts": {name: len(values) for name, values in inventories.items()},
    }
    result["digest"] = canonical_digest("CertifiedJL-release-lean-classification-v1", result)
    return result


def _copy_workspace(root: Path, workspace: Path, tracked: Sequence[Path]) -> None:
    workspace.mkdir(parents=True, exist_ok=False)
    for source in tracked:
        relative = source.relative_to(root)
        target = workspace / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    source_packages = root / ".lake" / "packages"
    target_packages = workspace / ".lake" / "packages"
    target_packages.mkdir(parents=True, exist_ok=False)
    for package in sorted(source_packages.iterdir()):
        (target_packages / package.name).symlink_to(
            package.resolve(strict=True), target_is_directory=True
        )
    project_build = workspace / ".lake" / "build"
    if project_build.exists() or project_build.is_symlink():
        raise ReleaseValidationError("isolated workspace project build was not initially absent")


def render_all_production(modules: Sequence[str]) -> str:
    if not modules or len(modules) != len(set(modules)):
        raise ReleaseValidationError("all-production root requires unique production modules")
    if GENERATED_MODULE in modules:
        raise ReleaseValidationError("generated all-production module collides with tracked source")
    return "\n".join([*(f"import {module}" for module in sorted(modules)), ""])


def compile_lean_scripts(root: Path, output: Path, lake: Path, lean: Path) -> None:
    """Elaborate tracked standalone Lean scripts without executing their mains."""
    classes = classify_lean_sources(root)
    sources = classes["scripts"]
    if not sources:
        raise ReleaseValidationError("release validation found no standalone Lean scripts")
    for source in sources:
        relative = source.relative_to(root).with_suffix(".olean")
        target = output / relative
        if target.exists() or target.is_symlink():
            raise ReleaseValidationError(f"standalone Lean script artifact already exists: {target}")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            [str(lake), "env", str(lean), str(source), "-o", str(target)],
            cwd=root, check=True,
        )


def preflight_library_module_targets(root: Path) -> None:
    """Check every non-script module belongs to a declared Lake library."""
    classes = classify_lean_sources(root)
    with (root / "lakefile.toml").open("rb") as stream:
        lakefile = __import__("tomllib").load(stream)
    libraries = {
        record.get("name") for record in lakefile.get("lean_lib", [])
        if isinstance(record, dict) and isinstance(record.get("name"), str)
    }
    modules = [
        module_name(root, source)
        for category in ("production_certifiedjl", "production_vendor", "certifiedjl_fast", "tests")
        for source in classes[category]
    ]
    missing = sorted(module for module in modules if module.split(".", 1)[0] not in libraries)
    if missing:
        raise ReleaseValidationError(f"modules are outside declared Lake libraries: {missing}")
    script_roots = sorted(module_name(root, source) for source in classes["scripts"])
    if any(module.split(".", 1)[0] in libraries for module in script_roots):
        raise ReleaseValidationError("standalone Lean scripts unexpectedly overlap a Lake library")
    print(
        f"preflight verified {len(modules)} Lake module targets and "
        f"{len(script_roots)} standalone Lean scripts"
    )


def _descendant_rss(root_pid: int) -> int:
    try:
        output = subprocess.check_output(
            ["ps", "-axo", "pid=,ppid=,rss="], text=True,
            stderr=subprocess.DEVNULL,
        )
    except (OSError, subprocess.CalledProcessError):
        return 0
    rows: list[tuple[int, int, int]] = []
    for line in output.splitlines():
        fields = line.split()
        if len(fields) != 3:
            continue
        try:
            rows.append(tuple(map(int, fields)))
        except ValueError:
            continue
    selected = {root_pid}
    changed = True
    while changed:
        changed = False
        for pid, ppid, _rss in rows:
            if ppid in selected and pid not in selected:
                selected.add(pid)
                changed = True
    return sum(rss * 1024 for pid, _ppid, rss in rows if pid in selected)


def _relative_artifact(path: Path, output_dir: Path) -> str:
    try:
        return path.relative_to(output_dir).as_posix()
    except ValueError as error:
        raise ReleaseValidationError(f"release artifact escaped output directory: {path}") from error


def run_command(
    *, name: str, command: Sequence[str], cwd: Path, environment: Mapping[str, str],
    log_path: Path, output_dir: Path, sample_seconds: float = 0.5,
) -> dict[str, object]:
    if log_path.exists() or log_path.is_symlink():
        raise ReleaseValidationError(f"release log already exists: {log_path}")
    log_path.parent.mkdir(parents=True, exist_ok=True)
    started_utc = utc_now()
    started = time.monotonic()
    peak_rss = 0
    interrupted: BaseException | None = None
    process: subprocess.Popen[bytes] | None = None

    def handle_signal(signum: int, _frame: object) -> None:
        # Cleanup after the first signal must be non-interruptible: a second
        # SIGINT/SIGTERM must not escape group termination and orphan children.
        if interrupted is not None:
            return
        raise InterruptedError(f"release validation received signal {signum}")

    previous_handlers: dict[signal.Signals, object] = {}
    for selected_signal in (signal.SIGINT, signal.SIGTERM):
        previous_handlers[selected_signal] = signal.signal(selected_signal, handle_signal)
    print(f"[release] start {name} log={log_path}", flush=True)
    try:
        with log_path.open("xb") as log:
            process = subprocess.Popen(
                list(command), cwd=cwd, env=dict(environment),
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
            )
            try:
                while process.poll() is None:
                    peak_rss = max(peak_rss, _descendant_rss(process.pid))
                    time.sleep(sample_seconds)
            except BaseException as error:
                interrupted = error
                try:
                    _stop_process_group(process)
                except BaseException as cleanup_error:
                    log.write(
                        (f"\nrelease validation cleanup error: {cleanup_error!r}\n")
                        .encode("utf-8", errors="replace")
                    )
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except OSError:
                        pass
                    try:
                        process.kill()
                    except OSError:
                        pass
            status = process.wait()
    finally:
        for selected_signal, handler in previous_handlers.items():
            signal.signal(selected_signal, handler)
    record: dict[str, object] = {
        "name": name,
        "command": list(command),
        "cwd": "isolated-workspace" if cwd.name == "workspace" else "release-output",
        "started_utc": started_utc,
        "finished_utc": utc_now(),
        "wall_seconds": round(time.monotonic() - started, 3),
        "peak_sampled_rss_bytes": peak_rss,
        "exit_code": status if interrupted is None else 130,
        "log": {
            "path": _relative_artifact(log_path, output_dir),
            "size_bytes": log_path.stat().st_size,
            "sha256": sha256_file(log_path),
        },
    }
    outcome = "interrupted" if interrupted is not None else ("passed" if status == 0 else "failed")
    print(
        f"[release] {outcome} {name} elapsed={record['wall_seconds']}s "
        f"peak_sampled_rss={record['peak_sampled_rss_bytes']}B",
        flush=True,
    )
    if interrupted is not None:
        raise ReleaseValidationError(
            f"release validation step was interrupted: {name}", step=record
        ) from interrupted
    if status != 0:
        raise ReleaseValidationError(f"release validation step failed: {name}", step=record)
    return record


def _stop_process_group(process: subprocess.Popen[object]) -> None:
    process_group = process.pid
    try:
        # A validation stage is disposable after interruption.  Kill the whole
        # owned session immediately so resistant descendants cannot outlive a
        # second interrupt or race the cooperative-grace probe.
        os.killpg(process_group, signal.SIGKILL)
    except ProcessLookupError:
        process.wait()
        return
    except OSError:
        # macOS can report EPERM while the last process-group member is
        # transitioning through exit.  Continue to direct-parent cleanup and
        # never let that diagnostic mask the validation interruption.
        pass
    if process.poll() is None:
        try:
            process.kill()
        except OSError:
            pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            process.kill()
        except OSError:
            pass
        process.wait()


def _artifact_inventory(workspace: Path, production_modules: Sequence[str]) -> dict[str, object]:
    build_lib = workspace / ".lake" / "build" / "lib" / "lean"
    expected = [Path(*module.split(".")).with_suffix(".olean") for module in production_modules]
    missing = [path.as_posix() for path in expected if not (build_lib / path).is_file()]
    actual = sorted(
        path.relative_to(build_lib)
        for path in build_lib.rglob("*.olean")
        if path.is_file() and not path.is_symlink()
    ) if build_lib.is_dir() else []
    expected_set = set(expected)
    unexpected = [path.as_posix() for path in actual if path not in expected_set]
    if missing:
        raise ReleaseValidationError(
            f"production build is missing {len(missing)} expected .olean artifacts: {missing[:10]}"
        )
    if unexpected:
        raise ReleaseValidationError(
            "production build emitted unexpected project .olean artifacts before generated roots: "
            f"{unexpected[:10]}"
        )
    records = [{
        "module": module,
        "path": (Path("workspace/.lake/build/lib/lean") / relative).as_posix(),
        "size_bytes": (build_lib / relative).stat().st_size,
        "sha256": sha256_file(build_lib / relative),
    } for module, relative in zip(production_modules, expected)]
    return {
        "expected_count": len(expected),
        "actual_count": len(actual),
        "complete": True,
        "unexpected_count": 0,
        "olean": records,
        "digest": canonical_digest("CertifiedJL-release-production-oleans-v1", records),
    }


def _classified_artifact_completeness(
    workspace: Path, category_modules: Mapping[str, Sequence[str]],
) -> dict[str, object]:
    build_lib = workspace / ".lake" / "build" / "lib" / "lean"
    expected_by_category = {
        name: [Path(*module.split(".")).with_suffix(".olean") for module in modules]
        for name, modules in category_modules.items()
    }
    missing = {
        name: [path.as_posix() for path in paths if not (build_lib / path).is_file()]
        for name, paths in expected_by_category.items()
    }
    missing = {name: paths for name, paths in missing.items() if paths}
    if missing:
        raise ReleaseValidationError(f"classified Lean artifacts are incomplete: {missing}")
    expected = {
        path for paths in expected_by_category.values() for path in paths
    } | {Path(f"{GENERATED_MODULE}.olean")}
    actual = {
        path.relative_to(build_lib) for path in build_lib.rglob("*.olean")
        if path.is_file() and not path.is_symlink()
    }
    if actual != expected:
        raise ReleaseValidationError(
            "complete Lean artifact set differs from classified sources: "
            f"missing={sorted(map(str, expected - actual))[:10]}, "
            f"unexpected={sorted(map(str, actual - expected))[:10]}"
        )
    payload = {
        "complete": True,
        "category_counts": {
            name: len(paths) for name, paths in expected_by_category.items()
        },
        "generated_count": 1,
        "expected_count": len(expected),
        "actual_count": len(actual),
    }
    return {**payload, "digest": canonical_digest(
        "CertifiedJL-release-classified-artifact-completeness-v1", payload
    )}


def _logical_tree_inventory(
    physical_root: Path, logical_prefix: str, *, skip: set[tuple[str, ...]] | None = None,
) -> list[dict[str, object]]:
    if not physical_root.is_dir():
        raise ReleaseValidationError(f"artifact tree is missing: {physical_root}")
    records: list[dict[str, object]] = []

    def visit(directory: Path, relative: Path, ancestors: frozenset[tuple[int, int]]) -> None:
        resolved_directory = directory.resolve(strict=True)
        identity = (resolved_directory.stat().st_dev, resolved_directory.stat().st_ino)
        if identity in ancestors:
            raise ReleaseValidationError(f"artifact tree contains a symlink cycle: {directory}")
        next_ancestors = ancestors | {identity}
        for child in sorted(directory.iterdir(), key=lambda path: path.name):
            child_relative = relative / child.name
            if skip and any(child_relative.parts[:len(parts)] == parts for parts in skip):
                continue
            try:
                resolved = child.resolve(strict=True)
            except OSError as error:
                raise ReleaseValidationError(f"broken artifact link: {child}") from error
            if resolved.is_dir():
                visit(child, child_relative, next_ancestors)
            elif resolved.is_file():
                mode = resolved.stat().st_mode
                records.append({
                    "path": f"{logical_prefix}/{child_relative.as_posix()}",
                    "size_bytes": resolved.stat().st_size,
                    "sha256": sha256_file(resolved),
                    "executable": bool(mode & stat.S_IXUSR),
                })
            else:
                raise ReleaseValidationError(f"artifact tree contains a special file: {child}")

    visit(physical_root, Path(), frozenset())
    return sorted(records, key=lambda record: str(record["path"]))


RELEASE_LEAN_ARTIFACT_SUFFIXES = (
    ".olean.private", ".olean.server", ".ir.sig",
    ".olean", ".ilean", ".ir",
)


def is_release_build_artifact(relative_to_build: Path) -> bool:
    """Select portable, reusable Lake build outputs for distribution."""
    if relative_to_build.is_absolute() or ".." in relative_to_build.parts:
        return False
    parts = relative_to_build.parts
    name = relative_to_build.name
    if parts[:2] == ("lib", "lean") and len(parts) > 2:
        return name.endswith(RELEASE_LEAN_ARTIFACT_SUFFIXES)
    if parts[:1] == ("lib",) and parts[:2] != ("lib", "lean") and len(parts) > 1:
        return (
            name.endswith((".dylib", ".dll", ".so"))
            or ".so." in name
        )
    return False


def _release_build_inventory(
    build_root: Path, logical_prefix: str,
) -> list[dict[str, object]]:
    if not build_root.is_dir():
        raise ReleaseValidationError(f"artifact build tree is missing: {build_root}")
    records: list[dict[str, object]] = []
    for relative in (Path("lib"),):
        physical = build_root / relative
        if not physical.exists():
            continue
        records.extend(_logical_tree_inventory(
            physical, f"{logical_prefix}/{relative.as_posix()}"
        ))
    prefix = logical_prefix.rstrip("/") + "/"
    selected = [
        record for record in records
        if is_release_build_artifact(Path(str(record["path"]).removeprefix(prefix)))
    ]
    return sorted(selected, key=lambda record: str(record["path"]))


def _package_manifest_digest(document: Mapping[str, object]) -> str:
    return canonical_digest(
        "CertifiedJL-release-package-source-manifest-v1",
        {key: value for key, value in document.items() if key != "manifest_digest"},
    )


def _git_tracked_regular_files(package_root: Path) -> tuple[Path, ...]:
    try:
        payload = subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=package_root, stderr=subprocess.DEVNULL,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise ReleaseValidationError(
            f"cannot enumerate tracked dependency sources: {package_root}"
        ) from error
    tracked_names = tuple(os.fsdecode(name) for name in payload.split(b"\0") if name)
    tracked_relative = {Path(name).as_posix() for name in tracked_names}
    result: list[Path] = []
    resolved_root = package_root.resolve(strict=True)
    for name in tracked_names:
        candidate = package_root / name
        if candidate.is_symlink():
            try:
                resolved = candidate.resolve(strict=True)
                target_relative = resolved.relative_to(resolved_root).as_posix()
            except (OSError, ValueError) as error:
                raise ReleaseValidationError(
                    f"tracked dependency symlink is broken or escapes its package: {candidate}"
                ) from error
            if not resolved.is_file():
                raise ReleaseValidationError(
                    f"tracked dependency symlink is not a regular file: {candidate}"
                )
            if target_relative not in tracked_relative:
                raise ReleaseValidationError(
                    f"tracked dependency symlink targets an untracked file: {candidate}"
                )
            result.append(candidate)
        elif candidate.is_file():
            result.append(candidate)
        elif not candidate.is_dir():
            raise ReleaseValidationError(f"tracked dependency source is missing: {candidate}")
    if not result:
        raise ReleaseValidationError(
            f"dependency has no tracked regular source files: {package_root}"
        )
    return tuple(result)


def _package_source_manifest_inventory(
    package_root: Path, paths: Iterable[Path],
) -> list[dict[str, object]]:
    records = []
    for path in sorted(set(paths)):
        resolved = path.resolve(strict=True)
        records.append({
            "path": path.relative_to(package_root).as_posix(),
            "size_bytes": resolved.stat().st_size,
            "sha256": sha256_file(resolved),
        })
    records.sort(key=lambda record: str(record["path"]))
    return records


def write_frozen_package_source_manifest(
    package_root: Path, output: Path | None = None,
) -> dict[str, object]:
    """Seal the tracked regular source files of one dependency checkout.

    The manifest lets a Git-free proof bundle reproduce the same dependency
    identity without treating ignored or untracked checkout files as proof
    inputs.  The manifest itself is deliberately excluded from that identity.
    """
    package_root = package_root.resolve(strict=True)
    records = _package_source_manifest_inventory(
        package_root, _git_tracked_regular_files(package_root)
    )
    document: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": "release-package-source-manifest",
        "files": records,
    }
    document["manifest_digest"] = _package_manifest_digest(document)
    destination = output or package_root / PACKAGE_SOURCE_MANIFEST_NAME
    destination.parent.mkdir(parents=True, exist_ok=True)
    _write_json_new(destination, document)
    return document


def _frozen_package_regular_files(package_root: Path) -> tuple[Path, ...]:
    manifest = package_root / PACKAGE_SOURCE_MANIFEST_NAME
    try:
        document = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReleaseValidationError(
            f"cannot read frozen dependency source manifest: {manifest}"
        ) from error
    if (
        not isinstance(document, dict)
        or set(document) != {"schema_version", "record_kind", "files", "manifest_digest"}
        or document["schema_version"] != SCHEMA_VERSION
        or document["record_kind"] != "release-package-source-manifest"
        or document["manifest_digest"] != _package_manifest_digest(document)
    ):
        raise ReleaseValidationError(f"invalid frozen dependency source manifest: {manifest}")
    _validate_inventory(document["files"], "frozen_package_source_manifest.files")
    result: list[Path] = []
    for record in document["files"]:
        candidate = package_root / record["path"]
        if (
            candidate.is_symlink() or not candidate.is_file()
            or candidate.stat().st_size != record["size_bytes"]
            or sha256_file(candidate) != record["sha256"]
        ):
            raise ReleaseValidationError(
                f"frozen dependency source differs: {record['path']}"
            )
        result.append(candidate)
    known = {path.resolve() for path in result}
    for candidate in package_root.rglob("*"):
        relative = candidate.relative_to(package_root)
        if (
            relative.parts[:2] == (".lake", "build")
            or relative.as_posix() == PACKAGE_SOURCE_MANIFEST_NAME
        ):
            continue
        if candidate.is_symlink() or (candidate.is_file() and candidate.resolve() not in known):
            raise ReleaseValidationError(
                f"dependency file is absent from frozen source manifest: {relative}"
            )
    if not result:
        raise ReleaseValidationError(f"frozen dependency source manifest is empty: {manifest}")
    return tuple(result)


def _package_source_inventory(
    package_root: Path, logical_prefix: str,
) -> list[dict[str, object]]:
    package_root = package_root.resolve(strict=True)
    if (package_root / ".git").exists():
        paths = _git_tracked_regular_files(package_root)
    else:
        paths = _frozen_package_regular_files(package_root)
    records = []
    for path in paths:
        relative = path.relative_to(package_root)
        resolved = path.resolve(strict=True)
        mode = resolved.stat().st_mode
        records.append({
            "path": f"{logical_prefix}/{relative.as_posix()}",
            "size_bytes": resolved.stat().st_size,
            "sha256": sha256_file(resolved),
            "executable": bool(mode & stat.S_IXUSR),
        })
    return sorted(records, key=lambda record: str(record["path"]))


def compute_artifact_identity(
    project_build: Path, packages_root: Path,
) -> dict[str, object]:
    """Hash the logical project/dependency source and artifact layout.

    Direct package symlinks are dereferenced under stable ``packages/NAME``
    prefixes, so an isolated validation workspace and a physically copied proof
    bundle have the same identity.  Each package contributes exactly its Git-
    tracked regular source files and the portable reusable portion of its
    ``.lake/build`` tree selected by :func:`is_release_build_artifact`.  Git
    administration, ignored/untracked files, nested package caches, traces,
    hashes, native intermediates, and tool executables are excluded.  A sealed
    per-package source manifest provides the identical selection contract after
    packaging removes Git administration.
    """
    project_files = _release_build_inventory(project_build, "project-build")
    if not packages_root.is_dir():
        raise ReleaseValidationError("artifact identity requires a package tree")
    package_names = sorted(path.name for path in packages_root.iterdir())
    if len(package_names) != len(set(package_names)):
        raise ReleaseValidationError("artifact package names are not unique")
    package_files: list[dict[str, object]] = []
    for name in package_names:
        package_root = packages_root / name
        logical_prefix = f"packages/{name}"
        package_files.extend(_package_source_inventory(package_root, logical_prefix))
        package_files.extend(_release_build_inventory(
            package_root / ".lake" / "build", f"{logical_prefix}/.lake/build"
        ))
    payload: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "identity_kind": "release-build-artifacts",
        "package_roots_dereferenced": package_names,
        "project_build_files": project_files,
        "package_files": sorted(package_files, key=lambda record: str(record["path"])),
    }
    payload["digest"] = canonical_digest("CertifiedJL-release-build-artifacts-v1", payload)
    return payload


def compute_validator_tool_identity(root: Path = ROOT) -> dict[str, object]:
    """Resolve and hash the Elan-selected executables named by lean-toolchain."""
    expected_toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    elan_candidate = shutil.which("elan")
    if elan_candidate is None:
        raise ReleaseValidationError("required release tool is missing: elan")
    elan_invocation = Path(elan_candidate).absolute()
    elan_resolved = elan_invocation.resolve(strict=True)
    tools: dict[str, object] = {}
    for executable in ("lean", "lake", "leanchecker"):
        selected_text = subprocess.check_output(
            [str(elan_invocation), "which", executable], cwd=root, text=True,
            stderr=subprocess.STDOUT,
        ).strip()
        selected = Path(selected_text).resolve(strict=True)
        if not selected.is_file():
            raise ReleaseValidationError(f"Elan selected no regular {executable} executable")
        tools[executable] = {
            "selected_path": str(selected),
            "relative_path": selected.relative_to(selected.parent.parent).as_posix(),
            "sha256": sha256_file(selected),
        }
    lean_version = subprocess.check_output(
        [str(tools["lean"]["selected_path"]), "--version"], cwd=root,
        text=True, stderr=subprocess.STDOUT,
    ).strip()
    lake_version = subprocess.check_output(
        [str(tools["lake"]["selected_path"]), "--version"], cwd=root,
        text=True, stderr=subprocess.STDOUT,
    ).strip()
    match = re.search(r":v([0-9]+(?:\.[0-9]+)+)$", expected_toolchain)
    if match is not None and f"version {match.group(1)}" not in lean_version:
        raise ReleaseValidationError("Elan-selected Lean version differs from lean-toolchain")
    tools["lean"]["version"] = lean_version
    tools["lake"]["version"] = lake_version
    tools["leanchecker"]["version"] = lean_version
    selected_roots = {
        Path(str(record["selected_path"])).parent.parent.resolve()
        for record in tools.values()
    }
    if len(selected_roots) != 1:
        raise ReleaseValidationError("Elan-selected validators do not share one toolchain")
    selected_root = selected_roots.pop()
    runtime = compute_toolchain_runtime_identity(selected_root)
    return {
        "lean_toolchain": expected_toolchain,
        "selected_toolchain_root": str(selected_root),
        **runtime,
        "elan": {
            "invocation_path": str(elan_invocation),
            "resolved_path": str(elan_resolved),
            "sha256": sha256_file(elan_resolved),
            "version": subprocess.check_output(
                [str(elan_invocation), "--version"], cwd=root, text=True,
                stderr=subprocess.STDOUT,
            ).strip(),
        },
        "executables": tools,
    }


def compute_toolchain_runtime_identity(toolchain_root: Path) -> dict[str, object]:
    runtime_files = []
    for directory in ("bin", "lib"):
        runtime_files.extend(_logical_tree_inventory(
            toolchain_root / directory, f"toolchain/{directory}"
        ))
    runtime_files.sort(key=lambda record: str(record["path"]))
    return {
        "runtime_file_count": len(runtime_files),
        "runtime_digest": canonical_digest(
            "CertifiedJL-release-toolchain-runtime-v1", runtime_files
        ),
    }


def verify_validator_tool_identity(
    record: Mapping[str, object], root: Path = ROOT,
) -> None:
    if validator_tool_portable_projection(record) != validator_tool_portable_projection(
        compute_validator_tool_identity(root)
    ):
        raise ValueError("release validator executables differ from the current pinned toolchain")


def validator_tool_portable_projection(
    record: Mapping[str, object],
) -> dict[str, object]:
    try:
        executables = record["executables"]
        elan = record["elan"]
        result = {
            "lean_toolchain": record["lean_toolchain"],
            "elan": {key: elan[key] for key in ("sha256", "version")},
            "executables": {
                name: {key: executables[name][key]
                       for key in ("relative_path", "sha256", "version")}
                for name in ("lean", "lake", "leanchecker")
            },
            "runtime_file_count": record["runtime_file_count"],
            "runtime_digest": record["runtime_digest"],
        }
    except (KeyError, TypeError) as error:
        raise ValueError("release validator tool identity is incomplete") from error
    for tool in result["executables"].values():
        _require_hash(tool["sha256"], "validator executable")
    _require_hash(result["elan"]["sha256"], "elan executable")
    _require_hash(result["runtime_digest"], "toolchain runtime")
    return result


def receipt_digest(receipt: Mapping[str, object]) -> str:
    return canonical_digest(
        "CertifiedJL-release-validation-receipt-v1",
        {key: value for key, value in receipt.items() if key != "receipt_digest"},
    )


def _write_json_new(path: Path, value: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def run_release_validation(root: Path, output_dir: Path) -> dict[str, object]:
    root = root.resolve()
    output_dir = output_dir.absolute()
    root_resolved = root.resolve()
    output_resolved = output_dir.resolve()
    if (
        output_resolved == root_resolved
        or root_resolved in output_resolved.parents
        or output_resolved in root_resolved.parents
    ):
        raise ReleaseValidationError("release output and source checkout must be disjoint")
    if output_dir.exists() or output_dir.is_symlink():
        raise ReleaseValidationError("release output directory must not already exist")

    commit = require_clean_checkout(root)
    tracked = tracked_files(root)
    classes = classify_lean_sources(root, tracked)
    identity_before = compute_release_identity(root)
    tool_identity = compute_validator_tool_identity(root)
    try:
        live_dependencies = list(verified_dependencies(root))
    except NativeReplayError as error:
        raise ReleaseValidationError(f"exact dependency verification failed: {error}") from error
    if [record["name"] for record in live_dependencies] != [
        record["name"] for record in identity_before["dependencies"]
    ]:
        raise ReleaseValidationError("live dependency inventory differs from release identity")

    output_dir.mkdir(parents=False)
    workspace = output_dir / "workspace"
    _copy_workspace(root, workspace, tracked)
    write_frozen_source_manifest(
        workspace, (workspace / path.relative_to(root) for path in tracked),
        workspace / SOURCE_MANIFEST_NAME,
    )
    if compute_release_identity(workspace) != identity_before:
        raise ReleaseValidationError("isolated workspace differs from release source identity")
    project_build = workspace / ".lake" / "build"
    if project_build.exists() or project_build.is_symlink():
        raise ReleaseValidationError("project build directory was not empty before validation")

    logs = output_dir / "logs"
    environment = os.environ.copy()
    environment.update({
        "LEAN_NUM_THREADS": "1",
        "LEAN_GC_THRESHOLD": environment.get("LEAN_GC_THRESHOLD", "256"),
        "LAKE_NO_CACHE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    })
    environment.pop("LAKE_ARTIFACT_CACHE", None)
    environment.pop("CERTIFIEDJL_NATIVE_BUILD_DIR", None)
    environment.pop("CERTIFIEDJL_NATIVE_SHADOW_DIR", None)
    steps: list[dict[str, object]] = []
    production_modules = list(identity_before["production_modules"])
    category_modules = {
        name: sorted(module_name(root, path) for path in paths)
        for name, paths in classes.items()
    }
    selected_tools = tool_identity["executables"]
    lake = str(selected_tools["lake"]["selected_path"])
    lean = str(selected_tools["lean"]["selected_path"])
    leanchecker = str(selected_tools["leanchecker"]["selected_path"])
    started = utc_now()
    failure: ReleaseValidationError | None = None
    artifacts: dict[str, object] = {}
    classified_artifacts: dict[str, object] = {}
    artifact_identity: dict[str, object] = {}
    reviewer_artifacts: dict[str, object] = {}
    try:
        steps.append(run_command(
            name="exact-dependency-check",
            command=[sys.executable, "scripts/check_dependency_cache.py"],
            cwd=workspace, environment=environment,
            log_path=logs / "00-exact-dependency-check.log", output_dir=output_dir,
        ))
        steps.append(run_command(
            name="production-source-trust-scan",
            command=[sys.executable, "scripts/check_trust.py"],
            cwd=workspace, environment=environment,
            log_path=logs / "01-production-source-trust-scan.log", output_dir=output_dir,
        ))
        steps.append(run_command(
            name="preflight-all-library-module-targets",
            command=[sys.executable, str(Path(__file__).resolve()),
                     "preflight-module-targets", "--root", "."],
            cwd=workspace, environment=environment,
            log_path=logs / "02-preflight-all-library-module-targets.log",
            output_dir=output_dir,
        ))
        build_command = [lake, "build", *production_modules]
        steps.append(run_command(
            name="explicit-all-production-module-build", command=build_command,
            cwd=workspace, environment=environment,
            log_path=logs / "03-all-production-build.log", output_dir=output_dir,
        ))
        artifacts = _artifact_inventory(workspace, production_modules)

        for index, (name, category) in enumerate((
            ("certifiedjl-fast", "certifiedjl_fast"),
            ("tests", "tests"),
        ), start=4):
            modules = category_modules[category]
            steps.append(run_command(
                name=f"explicit-all-{name}-module-build",
                command=[lake, "build", *modules],
                cwd=workspace, environment=environment,
                log_path=logs / f"{index:02d}-all-{name}-build.log",
                output_dir=output_dir,
            ))
        steps.append(run_command(
            name="elaborate-all-standalone-lean-scripts",
            command=[
                sys.executable, str(Path(__file__).resolve()), "compile-lean-scripts",
                "--root", ".", "--output", str(workspace / ".lake" / "build" / "lib" / "lean"),
                "--lake", lake, "--lean", lean,
            ],
            cwd=workspace, environment=environment,
            log_path=logs / "06-all-lean-scripts-elaboration.log",
            output_dir=output_dir,
        ))

        review_dir = workspace / ".lake" / "release-reviewer-workspace"
        steps.append(run_command(
            name="generate-reviewer-workspace",
            command=[sys.executable, "scripts/reviewer_workspace.py", "--root", ".",
                     "--output", str(review_dir)],
            cwd=workspace, environment=environment,
            log_path=logs / "07-generate-reviewer-workspace.log", output_dir=output_dir,
        ))
        review_source = review_dir / "Review.lean"
        theorem_map = review_dir / "theorem-map.json"
        review_olean = review_dir / "Review.olean"
        steps.append(run_command(
            name="compile-production-axiom-review",
            command=[lake, "env", lean, str(review_source), "-o", str(review_olean)],
            cwd=workspace, environment=environment,
            log_path=logs / "08-compile-production-axiom-review.log", output_dir=output_dir,
        ))
        reviewer_artifacts = {
            "review_lean": {
                "path": _relative_artifact(review_source, output_dir),
                "size_bytes": review_source.stat().st_size,
                "sha256": sha256_file(review_source),
            },
            "theorem_map": {
                "path": _relative_artifact(theorem_map, output_dir),
                "size_bytes": theorem_map.stat().st_size,
                "sha256": sha256_file(theorem_map),
            },
            "review_olean": {
                "path": _relative_artifact(review_olean, output_dir),
                "size_bytes": review_olean.stat().st_size,
                "sha256": sha256_file(review_olean),
            },
            "target_count": len(identity_before["reviewer_targets"]),
            "allowed_axioms": list(STANDARD_AXIOMS),
        }

        generated_dir = workspace / ".lake" / "release-generated"
        generated_dir.mkdir(parents=True, exist_ok=False)
        generated_source = generated_dir / f"{GENERATED_MODULE}.lean"
        generated_source.write_text(render_all_production(production_modules), encoding="utf-8")
        generated_olean = (
            workspace / ".lake" / "build" / "lib" / "lean" / f"{GENERATED_MODULE}.olean"
        )
        steps.append(run_command(
            name="compile-all-production-import-root",
            command=[lake, "env", lean, str(generated_source),
                     "-o", str(generated_olean)],
            cwd=workspace, environment=environment,
            log_path=logs / "09-compile-all-production-import-root.log",
            output_dir=output_dir,
        ))
        steps.append(run_command(
            name="leanchecker-fresh-single-thread-replay",
            command=[lake, "env", leanchecker, "--fresh", GENERATED_MODULE],
            cwd=workspace, environment=environment,
            log_path=logs / "10-leanchecker-fresh-single-thread-replay.log",
            output_dir=output_dir,
        ))
        classified_artifacts = _classified_artifact_completeness(
            workspace, category_modules
        )
        artifact_identity = compute_artifact_identity(
            workspace / ".lake" / "build", workspace / ".lake" / "packages"
        )
        generated = {
            "module": GENERATED_MODULE,
            "import_count": len(production_modules),
            "source": {
                "path": _relative_artifact(generated_source, output_dir),
                "size_bytes": generated_source.stat().st_size,
                "sha256": sha256_file(generated_source),
            },
            "olean": {
                "path": _relative_artifact(generated_olean, output_dir),
                "size_bytes": generated_olean.stat().st_size,
                "sha256": sha256_file(generated_olean),
            },
            "leanchecker_fresh": True,
            "lean_num_threads": "1",
        }
    except ReleaseValidationError as error:
        failure = error
        if error.step is not None:
            steps.append(error.step)
        generated = {}

    identity_after = compute_release_identity(root)
    workspace_identity_after = compute_release_identity(workspace)
    source_unchanged = (
        identity_after == identity_before
        and workspace_identity_after == identity_before
        and require_clean_checkout(root) == commit
    )
    tools_unchanged = False
    dependencies_unchanged = False
    try:
        tools_unchanged = compute_validator_tool_identity(root) == tool_identity
    except ReleaseValidationError as error:
        if failure is None:
            failure = ReleaseValidationError(
                f"validator toolchain could not be rechecked after validation: {error}"
            )
    try:
        dependencies_unchanged = list(verified_dependencies(root)) == live_dependencies
    except NativeReplayError as error:
        if failure is None:
            failure = ReleaseValidationError(
                f"dependencies could not be rechecked after validation: {error}"
            )
    if failure is None and not source_unchanged:
        failure = ReleaseValidationError("release source inputs changed during validation")
    if failure is None and not tools_unchanged:
        failure = ReleaseValidationError("validator toolchain changed during validation")
    if failure is None and not dependencies_unchanged:
        failure = ReleaseValidationError("dependency inputs changed during validation")
    classification = _classification_document(root, classes)
    common: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": RECORD_KIND,
        "attests_execution": failure is None,
        "success": failure is None,
        "mode": "release",
        "source_identity": identity_before,
        "source_commit": commit,
        "source_classification": classification,
        "build": {
            "claim": "fresh-project-build-with-preverified-dependency-artifacts",
            "cold_scope": "project-artifacts-only",
            "workspace_project_build_initially_absent": True,
            "dependency_artifacts_reused": True,
            "explicit_production_module_count": len(production_modules),
            "explicit_nonproduction_module_counts": {
                category: len(category_modules[category])
                for category in ("certifiedjl_fast", "tests", "scripts")
            },
            "all_production_modules_explicit": True,
            "fast_and_test_modules_excluded": True,
            "project_artifacts": artifacts,
            "all_classified_lean_artifacts": classified_artifacts,
        },
        "artifact_identity": artifact_identity,
        "reviewer_workspace": reviewer_artifacts,
        "all_production_import_root": generated,
        "environment": {
            "os": platform.system(),
            "os_release": platform.release(),
            "architecture": platform.machine(),
            "python_version": platform.python_version(),
            "lean_num_threads": "1",
            "lake_no_cache": "1",
            "tools": tool_identity,
            "verified_dependencies": live_dependencies,
        },
        "execution": {
            "started_utc": started,
            "finished_utc": utc_now(),
            "source_unchanged": source_unchanged,
            "tools_unchanged": tools_unchanged,
            "dependencies_unchanged": dependencies_unchanged,
            "steps": steps,
            "step_count": len(steps),
        },
    }
    if failure is not None:
        common["failure"] = str(failure)
        common["receipt_digest"] = receipt_digest(common)
        _write_json_new(output_dir / FAILURE_NAME, common)
        raise failure
    common["receipt_digest"] = receipt_digest(common)
    verify_release_receipt_document(common, expected_proof_identity=identity_before)
    _write_json_new(output_dir / RECEIPT_NAME, common)
    return common


def _require_hash(value: object, field: str) -> None:
    if not isinstance(value, str) or HASH.fullmatch(value) is None:
        raise ValueError(f"invalid release receipt hash: {field}")


def _validate_inventory(value: object, field: str) -> None:
    if not isinstance(value, list):
        raise ValueError(f"invalid release receipt inventory: {field}")
    paths: list[str] = []
    for record in value:
        if not isinstance(record, dict) or set(record) != {"path", "size_bytes", "sha256"}:
            raise ValueError(f"invalid release receipt inventory entry: {field}")
        path = record["path"]
        if (
            not isinstance(path, str) or not path or Path(path).is_absolute()
            or ".." in Path(path).parts
            or not isinstance(record["size_bytes"], int)
            or isinstance(record["size_bytes"], bool)
            or record["size_bytes"] < 0
        ):
            raise ValueError(f"invalid release receipt inventory entry: {field}")
        _require_hash(record["sha256"], f"{field}.{path}")
        paths.append(path)
    if paths != sorted(set(paths)):
        raise ValueError(f"release receipt inventory is not uniquely sorted: {field}")


def _validate_classification(value: object) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != {
        "all_tracked_lean_sources_classified", "categories", "counts", "digest"
    }:
        raise ValueError("release Lean source classification is incomplete")
    expected_categories = {
        "production_certifiedjl", "production_vendor", "tests",
        "certifiedjl_fast", "scripts",
    }
    categories = value["categories"]
    counts = value["counts"]
    if (
        value["all_tracked_lean_sources_classified"] is not True
        or not isinstance(categories, dict) or set(categories) != expected_categories
        or not isinstance(counts, dict) or set(counts) != expected_categories
    ):
        raise ValueError("release Lean source categories are invalid")
    all_paths: list[str] = []
    for name in sorted(expected_categories):
        _validate_inventory(categories[name], f"lean_source_classification.{name}")
        if counts[name] != len(categories[name]):
            raise ValueError(f"release Lean source count differs for {name}")
        for record in categories[name]:
            path = Path(str(record["path"]))
            if lean_source_class(path) != name:
                raise ValueError(f"misclassified release Lean source: {path}")
            all_paths.append(path.as_posix())
    if len(all_paths) != len(set(all_paths)):
        raise ValueError("release Lean source categories overlap")
    expected_digest = canonical_digest(
        "CertifiedJL-release-lean-classification-v1",
        {key: item for key, item in value.items() if key != "digest"},
    )
    if value["digest"] != expected_digest:
        raise ValueError("release Lean source classification digest mismatch")
    return value


def _validate_source_identity(identity: object) -> dict[str, object]:
    if not isinstance(identity, dict):
        raise ValueError("release receipt has no source identity")
    required = {
        "schema_version", "identity_kind", "mode", "proof_closure_digest",
        "validation_procedure_digest", "validation_digest", "digest", "proof_inputs",
        "procedure_inputs", "dependencies", "production_modules", "reviewer_targets",
        "lean_source_classification", "paper_and_docs_excluded",
    }
    if set(identity) != required:
        raise ValueError("release source identity fields are incomplete")
    if (
        identity["schema_version"] != SCHEMA_VERSION
        or identity["identity_kind"] != IDENTITY_KIND
        or identity["mode"] != "release"
        or identity["paper_and_docs_excluded"] is not True
    ):
        raise ValueError("invalid release source identity header")
    _validate_inventory(identity["proof_inputs"], "proof_inputs")
    _validate_inventory(identity["procedure_inputs"], "procedure_inputs")
    if any(
        str(record["path"]).startswith(("paper/", "docs/"))
        for field in ("proof_inputs", "procedure_inputs")
        for record in identity[field]
    ):
        raise ValueError("paper or docs entered release validation identity")
    dependencies = identity["dependencies"]
    modules = identity["production_modules"]
    targets = identity["reviewer_targets"]
    classification = _validate_classification(identity["lean_source_classification"])
    if not isinstance(dependencies, list) or not isinstance(modules, list) or not isinstance(targets, list):
        raise ValueError("release source identity lists are invalid")
    if not modules or modules != sorted(set(modules)) or not all(isinstance(v, str) for v in modules):
        raise ValueError("release production module identity is invalid")
    proof_expected = canonical_digest("CertifiedJL-release-proof-closure-v1", {
        "inputs": identity["proof_inputs"],
        "dependencies": dependencies,
        "production_modules": modules,
    })
    procedure_expected = canonical_digest("CertifiedJL-release-procedure-v1", {
        "inputs": identity["procedure_inputs"],
        "reviewer_targets": targets,
        "lean_source_classification_digest": classification.get("digest")
        if isinstance(classification, dict) else None,
        "standard_axioms": list(STANDARD_AXIOMS),
        "all_production_module": GENERATED_MODULE,
        "leanchecker": {"fresh": True, "lean_num_threads": "1"},
    })
    validation_expected = canonical_digest("CertifiedJL-release-validation-inputs-v1", {
        "proof_closure_digest": proof_expected,
        "validation_procedure_digest": procedure_expected,
    })
    if identity["proof_closure_digest"] != proof_expected:
        raise ValueError("release proof identity digest mismatch")
    if identity["validation_procedure_digest"] != procedure_expected:
        raise ValueError("release procedure identity digest mismatch")
    if identity["validation_digest"] != validation_expected or identity["digest"] != validation_expected:
        raise ValueError("release validation identity digest mismatch")
    expected_modules = sorted(
        Path(record["path"]).with_suffix("").as_posix().replace("/", ".")
        for name in ("production_certifiedjl", "production_vendor")
        for record in classification["categories"][name]
    )
    if modules != expected_modules:
        raise ValueError("release production module list differs from classified sources")
    return identity


def receipt_semantics(
    receipt: Mapping[str, object],
) -> tuple[dict[str, object], dict[str, object], str]:
    identity = _validate_source_identity(receipt.get("source_identity"))
    artifacts = _validate_artifact_identity(receipt.get("artifact_identity"))
    digest = receipt.get("receipt_digest")
    _require_hash(digest, "receipt_digest")
    assert isinstance(digest, str)
    return identity, artifacts, digest


def _validate_artifact_identity(value: object) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != {
        "schema_version", "identity_kind", "package_roots_dereferenced",
        "project_build_files", "package_files", "digest",
    }:
        raise ValueError("release build artifact identity is incomplete")
    if (
        value["schema_version"] != SCHEMA_VERSION
        or value["identity_kind"] != "release-build-artifacts"
        or not isinstance(value["package_roots_dereferenced"], list)
        or value["package_roots_dereferenced"]
        != sorted(set(value["package_roots_dereferenced"]))
    ):
        raise ValueError("release build artifact identity header is invalid")
    all_paths: list[str] = []
    for field, prefix in (("project_build_files", "project-build/"),
                          ("package_files", "packages/")):
        records = value[field]
        if not isinstance(records, list):
            raise ValueError(f"release artifact inventory is invalid: {field}")
        paths = []
        for record in records:
            if not isinstance(record, dict) or set(record) != {
                "path", "size_bytes", "sha256", "executable"
            }:
                raise ValueError(f"release artifact record is invalid: {field}")
            path = record["path"]
            if (
                not isinstance(path, str) or not path.startswith(prefix)
                or Path(path).is_absolute() or ".." in Path(path).parts
                or not isinstance(record["size_bytes"], int)
                or isinstance(record["size_bytes"], bool)
                or record["size_bytes"] < 0
                or not isinstance(record["executable"], bool)
            ):
                raise ValueError(f"release artifact record fields are invalid: {field}")
            _require_hash(record["sha256"], f"artifact.{path}")
            paths.append(path)
        if paths != sorted(set(paths)):
            raise ValueError(f"release artifact inventory is not uniquely sorted: {field}")
        all_paths.extend(paths)
    if len(all_paths) != len(set(all_paths)):
        raise ValueError("release artifact inventories overlap")
    expected = canonical_digest(
        "CertifiedJL-release-build-artifacts-v1",
        {key: item for key, item in value.items() if key != "digest"},
    )
    if value["digest"] != expected:
        raise ValueError("release build artifact identity digest mismatch")
    return value


def verify_release_receipt_document(
    receipt: object, *, expected_proof_identity: Mapping[str, object] | None = None,
) -> dict[str, object]:
    if not isinstance(receipt, dict):
        raise ValueError("release receipt must be a JSON object")
    required = {
        "schema_version", "record_kind", "attests_execution", "success", "mode",
        "source_identity", "source_commit", "source_classification", "build",
        "artifact_identity", "reviewer_workspace", "all_production_import_root",
        "environment", "execution",
        "receipt_digest",
    }
    if set(receipt) != required:
        raise ValueError("release receipt fields are incomplete")
    if (
        receipt["schema_version"] != SCHEMA_VERSION
        or receipt["record_kind"] != RECORD_KIND
        or receipt["attests_execution"] is not True
        or receipt["success"] is not True
        or receipt["mode"] != "release"
    ):
        raise ValueError("release receipt is not a successful release attestation")
    identity = _validate_source_identity(receipt["source_identity"])
    classification = _validate_classification(receipt["source_classification"])
    if classification != identity["lean_source_classification"]:
        raise ValueError("release receipt classification is not bound to source identity")
    if expected_proof_identity is not None:
        expected = dict(expected_proof_identity)
        if expected.get("identity_kind") == "proof-bundle-inputs":
            if proof_identity_projection(identity) != expected:
                raise ValueError("release receipt proof projection differs from expected identity")
        elif identity != expected:
            raise ValueError("release receipt source identity differs from expected identity")
    if receipt["receipt_digest"] != receipt_digest(receipt):
        raise ValueError("release receipt self-digest mismatch")
    _validate_artifact_identity(receipt["artifact_identity"])

    build = receipt["build"]
    if not isinstance(build, dict) or not all((
        build.get("claim") == "fresh-project-build-with-preverified-dependency-artifacts",
        build.get("cold_scope") == "project-artifacts-only",
        build.get("workspace_project_build_initially_absent") is True,
        build.get("dependency_artifacts_reused") is True,
        build.get("all_production_modules_explicit") is True,
        build.get("fast_and_test_modules_excluded") is True,
    )):
        raise ValueError("release receipt does not attest the required fresh project build")
    artifacts = build.get("project_artifacts")
    if (
        not isinstance(artifacts, dict)
        or artifacts.get("complete") is not True
        or artifacts.get("unexpected_count") != 0
        or artifacts.get("expected_count") != artifacts.get("actual_count")
        or artifacts.get("expected_count") != build.get("explicit_production_module_count")
    ):
        raise ValueError("release receipt production artifact set is incomplete")
    oleans = artifacts.get("olean")
    if not isinstance(oleans, list) or len(oleans) != artifacts["expected_count"]:
        raise ValueError("release receipt production artifact inventory is incomplete")
    if artifacts.get("digest") != canonical_digest(
        "CertifiedJL-release-production-oleans-v1", oleans
    ):
        raise ValueError("release receipt production artifact digest mismatch")
    expected_olean_paths = [
        (Path("workspace/.lake/build/lib/lean")
         / Path(*module.split(".")).with_suffix(".olean")).as_posix()
        for module in identity["production_modules"]
    ]
    for module, path, record in zip(identity["production_modules"], expected_olean_paths, oleans):
        if (
            not isinstance(record, dict)
            or set(record) != {"module", "path", "size_bytes", "sha256"}
            or record["module"] != module or record["path"] != path
            or not isinstance(record["size_bytes"], int) or record["size_bytes"] <= 0
        ):
            raise ValueError("release production .olean inventory is not exact")
        _require_hash(record["sha256"], f"production_olean.{module}")
    classified_artifacts = build.get("all_classified_lean_artifacts")
    category_counts = classification["counts"]
    if (
        not isinstance(classified_artifacts, dict)
        or classified_artifacts.get("complete") is not True
        or classified_artifacts.get("category_counts") != category_counts
        or classified_artifacts.get("generated_count") != 1
        or classified_artifacts.get("expected_count")
        != sum(category_counts.values()) + 1
        or classified_artifacts.get("actual_count")
        != classified_artifacts.get("expected_count")
    ):
        raise ValueError("release classified Lean artifact completeness is invalid")
    expected_classified_digest = canonical_digest(
        "CertifiedJL-release-classified-artifact-completeness-v1",
        {key: item for key, item in classified_artifacts.items() if key != "digest"},
    )
    if classified_artifacts.get("digest") != expected_classified_digest:
        raise ValueError("release classified Lean artifact completeness digest mismatch")

    execution = receipt["execution"]
    if (
        not isinstance(execution, dict)
        or execution.get("source_unchanged") is not True
        or execution.get("tools_unchanged") is not True
        or execution.get("dependencies_unchanged") is not True
        or execution.get("step_count") != 11
        or not isinstance(execution.get("steps"), list)
        or len(execution["steps"]) != 11
    ):
        raise ValueError("release receipt execution record is incomplete")
    expected_steps = [
        "exact-dependency-check", "production-source-trust-scan",
        "preflight-all-library-module-targets",
        "explicit-all-production-module-build",
        "explicit-all-certifiedjl-fast-module-build",
        "explicit-all-tests-module-build", "elaborate-all-standalone-lean-scripts",
        "generate-reviewer-workspace",
        "compile-production-axiom-review", "compile-all-production-import-root",
        "leanchecker-fresh-single-thread-replay",
    ]
    for expected, step in zip(expected_steps, execution["steps"]):
        if not isinstance(step, dict) or step.get("name") != expected or step.get("exit_code") != 0:
            raise ValueError(f"release receipt step did not succeed in order: {expected}")
        if (
            not isinstance(step.get("wall_seconds"), (int, float))
            or step["wall_seconds"] < 0
            or not isinstance(step.get("peak_sampled_rss_bytes"), int)
            or step["peak_sampled_rss_bytes"] < 0
        ):
            raise ValueError(f"release receipt step metrics are invalid: {expected}")
        log = step.get("log")
        if not isinstance(log, dict):
            raise ValueError(f"release receipt step has no log: {expected}")
        _require_hash(log.get("sha256"), f"{expected}.log")
    tools = receipt["environment"].get("tools") if isinstance(receipt["environment"], dict) else None
    if not isinstance(tools, dict):
        raise ValueError("release receipt has no validator tool identity")
    validator_tool_portable_projection(tools)
    lake = tools["executables"]["lake"]["selected_path"]
    lean = tools["executables"]["lean"]["selected_path"]
    leanchecker = tools["executables"]["leanchecker"]["selected_path"]
    preflight = execution["steps"][2].get("command")
    if (
        not isinstance(preflight, list)
        or len(preflight) != 5
        or Path(preflight[1]).name != "release_validation.py"
        or preflight[2:] != ["preflight-module-targets", "--root", "."]
    ):
        raise ValueError("release receipt did not preflight every Lake module target")
    build_command = execution["steps"][3].get("command")
    if build_command != [lake, "build", *identity["production_modules"]]:
        raise ValueError("release receipt build command is not the explicit production module list")
    for index, category in ((4, "certifiedjl_fast"), (5, "tests")):
        modules = [
            Path(record["path"]).with_suffix("").as_posix().replace("/", ".")
            for record in classification["categories"][category]
        ]
        if execution["steps"][index].get("command") != [lake, "build", *modules]:
            raise ValueError(f"release receipt does not explicitly build category: {category}")
    script_command = execution["steps"][6].get("command")
    if (
        not isinstance(script_command, list)
        or len(script_command) < 8
        or Path(script_command[1]).name != "release_validation.py"
        or script_command[2:4] != ["compile-lean-scripts", "--root"]
        or script_command[-4:] != ["--lake", lake, "--lean", lean]
    ):
        raise ValueError("release receipt did not elaborate standalone Lean scripts")
    for index in (8, 9):
        command = execution["steps"][index].get("command")
        if not isinstance(command, list) or command[:3] != [lake, "env", lean]:
            raise ValueError("release receipt did not use the selected Lean executable")
    checker = execution["steps"][10].get("command")
    if checker != [lake, "env", leanchecker, "--fresh", GENERATED_MODULE]:
        raise ValueError("release receipt did not run leanchecker --fresh on the generated root")

    artifact_identity = _validate_artifact_identity(receipt["artifact_identity"])
    if artifact_identity["package_roots_dereferenced"] != [
        record["name"] for record in identity["dependencies"]
    ]:
        raise ValueError("release artifact package roots differ from pinned dependencies")
    build_artifact_by_path = {
        record["path"]: record for record in artifact_identity["project_build_files"]
    }
    for record in oleans:
        logical = str(record["path"]).removeprefix("workspace/.lake/build/")
        bound = build_artifact_by_path.get("project-build/" + logical)
        if (
            bound is None or bound["sha256"] != record["sha256"]
            or bound["size_bytes"] != record["size_bytes"]
        ):
            raise ValueError("release production .olean differs from build artifact identity")

    generated = receipt["all_production_import_root"]
    if (
        not isinstance(generated, dict)
        or generated.get("module") != GENERATED_MODULE
        or generated.get("import_count") != len(identity["production_modules"])
        or generated.get("leanchecker_fresh") is not True
        or generated.get("lean_num_threads") != "1"
    ):
        raise ValueError("release receipt all-production replay is incomplete")
    for field in ("source", "olean"):
        record = generated.get(field)
        if (
            not isinstance(record, dict)
            or set(record) != {"path", "size_bytes", "sha256"}
            or not isinstance(record["path"], str)
            or Path(record["path"]).is_absolute()
            or not isinstance(record["size_bytes"], int) or record["size_bytes"] <= 0
        ):
            raise ValueError(f"release generated root artifact is invalid: {field}")
        _require_hash(record["sha256"], f"all_production_import_root.{field}")
    generated_bound = build_artifact_by_path.get(
        f"project-build/lib/lean/{GENERATED_MODULE}.olean"
    )
    if (
        generated_bound is None
        or generated_bound["sha256"] != generated["olean"]["sha256"]
        or generated_bound["size_bytes"] != generated["olean"]["size_bytes"]
    ):
        raise ValueError("generated root .olean differs from build artifact identity")
    reviewer = receipt["reviewer_workspace"]
    if (
        not isinstance(reviewer, dict)
        or reviewer.get("target_count") != len(identity["reviewer_targets"])
        or reviewer.get("allowed_axioms") != list(STANDARD_AXIOMS)
    ):
        raise ValueError("release receipt reviewer audit is incomplete")
    for field in ("review_lean", "theorem_map", "review_olean"):
        record = reviewer.get(field)
        if not isinstance(record, dict):
            raise ValueError(f"release receipt reviewer artifact is missing: {field}")
        _require_hash(record.get("sha256"), f"reviewer_workspace.{field}")
    environment = receipt["environment"]
    if (
        not isinstance(environment, dict)
        or environment.get("lean_num_threads") != "1"
        or environment.get("lake_no_cache") != "1"
        or not isinstance(environment.get("verified_dependencies"), list)
        or len(environment["verified_dependencies"]) != len(identity["dependencies"])
    ):
        raise ValueError("release receipt execution environment is incomplete")
    _verify_dependency_records(
        environment["verified_dependencies"], identity["dependencies"]
    )
    return receipt


def _verify_dependency_records(
    live_dependencies: Sequence[Mapping[str, object]],
    expected_dependencies: Sequence[Mapping[str, object]],
) -> None:
    if [record.get("name") for record in live_dependencies] != [
        record.get("name") for record in expected_dependencies
    ]:
        raise ValueError("release receipt dependency names differ from source identity")
    for live, expected in zip(live_dependencies, expected_dependencies):
        if (
            live.get("type") != "git"
            or live.get("expected_url") != expected.get("url")
            or live.get("actual_url") != expected.get("url")
            or live.get("expected_revision") != expected.get("rev")
            or live.get("actual_revision") != expected.get("rev")
            # native_shadow_replay.verified_dependencies uses the established
            # bare hexadecimal Git-status digest schema.
            or live.get("status_sha256") != hashlib.sha256(b"").hexdigest()
        ):
            raise ValueError(f"release receipt dependency is not exact: {expected.get('name')}")


def verify_release_receipt(
    path: Path, *, expected_proof_identity: Mapping[str, object] | None = None,
    evidence_root: Path | None = None,
    check_live_tools: bool = False, tool_root: Path | None = None,
) -> dict[str, object]:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read release receipt {path}: {error}") from error
    receipt = verify_release_receipt_document(
        document, expected_proof_identity=expected_proof_identity
    )
    verify_validation_evidence(
        receipt, path.parent if evidence_root is None else evidence_root
    )
    if check_live_tools:
        verify_validator_tool_identity(
            receipt["environment"]["tools"], ROOT if tool_root is None else tool_root
        )
    return receipt


def validation_evidence_inventory(
    receipt: Mapping[str, object],
) -> list[dict[str, object]]:
    """Return every receipt-relative log/generated artifact bound by the receipt."""
    records: list[dict[str, object]] = []
    try:
        for step in receipt["execution"]["steps"]:
            records.append(dict(step["log"]))
        reviewer = receipt["reviewer_workspace"]
        for field in ("review_lean", "theorem_map", "review_olean"):
            records.append(dict(reviewer[field]))
        generated = receipt["all_production_import_root"]
        for field in ("source", "olean"):
            records.append(dict(generated[field]))
    except (KeyError, TypeError) as error:
        raise ValueError("release validation evidence inventory is incomplete") from error
    records.sort(key=lambda record: str(record.get("path", "")))
    _validate_inventory(records, "validation_evidence")
    return records


def verify_validation_evidence(
    receipt: Mapping[str, object], evidence_root: Path,
) -> None:
    root = evidence_root.resolve()
    for record in validation_evidence_inventory(receipt):
        candidate = evidence_root / str(record["path"])
        try:
            resolved = candidate.resolve(strict=True)
            resolved.relative_to(root)
        except (OSError, ValueError) as error:
            raise ValueError(f"release evidence path escapes or is missing: {record['path']}") from error
        if (
            candidate.is_symlink() or not candidate.is_file()
            or candidate.stat().st_size != record["size_bytes"]
            or sha256_file(candidate) != record["sha256"]
        ):
            raise ValueError(f"release evidence bytes differ: {record['path']}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    identity_parser = subparsers.add_parser("identity")
    identity_parser.add_argument("--root", type=Path, default=ROOT)
    identity_parser.add_argument("--json", action="store_true")
    run_parser = subparsers.add_parser("run")
    run_parser.add_argument("--root", type=Path, default=ROOT)
    run_parser.add_argument("--output-dir", type=Path, required=True)
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("receipt", type=Path)
    verify_parser.add_argument("--expected-proof-identity", type=Path)
    verify_parser.add_argument("--check-live-tools", action="store_true")
    verify_parser.add_argument("--tool-root", type=Path)
    scripts_parser = subparsers.add_parser("compile-lean-scripts", help=argparse.SUPPRESS)
    scripts_parser.add_argument("--root", type=Path, required=True)
    scripts_parser.add_argument("--output", type=Path, required=True)
    scripts_parser.add_argument("--lake", type=Path, required=True)
    scripts_parser.add_argument("--lean", type=Path, required=True)
    preflight_parser = subparsers.add_parser("preflight-module-targets", help=argparse.SUPPRESS)
    preflight_parser.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "identity":
            identity = compute_release_identity(args.root)
            if args.json:
                print(json.dumps(identity, indent=2, sort_keys=True))
            else:
                for key in ("proof_closure_digest", "validation_procedure_digest",
                            "validation_digest"):
                    print(f"{key}={identity[key]}")
        elif args.command == "run":
            receipt = run_release_validation(args.root, args.output_dir)
            print(f"release validation passed: {receipt['receipt_digest']}")
        elif args.command == "verify":
            expected = None
            if args.expected_proof_identity is not None:
                expected = json.loads(args.expected_proof_identity.read_text(encoding="utf-8"))
            receipt = verify_release_receipt(
                args.receipt, expected_proof_identity=expected,
                check_live_tools=args.check_live_tools, tool_root=args.tool_root,
            )
            print(f"release receipt verified: {receipt['receipt_digest']}")
        elif args.command == "compile-lean-scripts":
            compile_lean_scripts(args.root.resolve(), args.output, args.lake, args.lean)
        else:
            preflight_library_module_targets(args.root.resolve())
    except (ReleaseValidationError, ValueError) as error:
        raise SystemExit(f"release validation error: {error}") from error


if __name__ == "__main__":
    main()
