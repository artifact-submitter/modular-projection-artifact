#!/usr/bin/env python3
"""Create and verify execution receipts for the serial kernel proof record."""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
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
from typing import Any, BinaryIO
import uuid


def _python_cache_isolation_active() -> bool:
    """Return whether local modules cannot use a source-tree bytecode cache."""
    if not sys.dont_write_bytecode or not sys.pycache_prefix:
        return False
    prefix = Path(sys.pycache_prefix).absolute()
    repository = Path(__file__).resolve().parent.parent
    try:
        prefix.relative_to(repository)
        return False
    except ValueError:
        return not prefix.exists()


def _restart_with_python_cache_isolation() -> None:
    """Re-exec before importing repository modules under a fresh external cache."""
    if __name__ != "__main__" or _python_cache_isolation_active():
        return
    environment = os.environ.copy()
    prefix = Path(os.environ.get("TMPDIR", "/tmp")) / (
        f"certifiedjl-disabled-pycache-{uuid.uuid4().hex}"
    )
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPYCACHEPREFIX"] = str(prefix.absolute())
    os.execve(
        sys.executable,
        [sys.executable, "-B", str(Path(__file__).absolute()), *sys.argv[1:]],
        environment,
    )


_restart_with_python_cache_isolation()

try:
    import tomllib
except ModuleNotFoundError as exc:  # pragma: no cover
    raise SystemExit("Python 3.11 or newer is required") from exc

from compute_replay_digest import (
    ROOT,
    canonical_digest,
    closure,
    digest_files,
    import_graph,
    module_source,
    require_clean_source,
    require_tracked_closure,
    tracked_sources,
    validate_identity_document,
)
from native_shadow_replay import NativeReplayError, verified_dependencies


SCHEMA_VERSION = 1
RECEIPT_NAME = "stage-receipt.json"
LOG_NAME = "stage.log"
SOURCE_IDENTITY_NAME = "source-inputs.json"
EXECUTION_RECORD_NAME = "kernel-proof-record.json"
SELECTION_NAME = "stage-selection.json"
KERNEL_CACHE_PREFIX = "v6-mode-kernel-proof-record-"
DEFAULT_LEAN_NUM_THREADS = "2"
DEFAULT_LEAN_GC_THRESHOLD = "256"


def require_python_cache_isolation() -> None:
    if not _python_cache_isolation_active():
        raise ValueError(
            "kernel receipt execution requires isolated Python bytecode caching"
        )


@dataclass(frozen=True)
class StagePlan:
    index: int
    name: str
    script: str
    timeout_minutes: int

    @property
    def command(self) -> list[str]:
        return [
            "timeout",
            "--signal=INT",
            "--kill-after=5m",
            f"{self.timeout_minutes}m",
            f"./{self.script}",
        ]


STAGE_PLAN = (
    StagePlan(0, "evidence", "scripts/validate_certificate_evidence.sh", 90),
    StagePlan(1, "moderate", "scripts/validate_certificate_moderate.sh", 330),
    StagePlan(2, "ternary-upper", "scripts/validate_certificate_ternary_upper.sh", 150),
    StagePlan(3, "library", "scripts/validate_certificate_library.sh", 330),
    StagePlan(4, "complete", "scripts/validate_certificate_canaries.sh", 330),
)
PLAN_BY_NAME = {stage.name: stage for stage in STAGE_PLAN}
REPLAY_ENV_KEYS = (
    "CERTIFIEDJL_MODERATE_BATCH_SIZE",
    "CERTIFIEDJL_MODERATE_JOBS",
    "CERTIFIEDJL_KERNEL_CANARY_BATCH_SIZE",
    "CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE",
    "CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE",
    "CI",
    "LAKE_ARTIFACT_CACHE",
    "LAKE_NO_CACHE",
    "LEAN_OPTS",
    "LEAN_PATH",
    "LEAN_SRC_PATH",
    "LEAN_NUM_THREADS",
    "LEAN_GC_THRESHOLD",
    "PATH",
    "ELAN_TOOLCHAIN",
    "PYTHONHASHSEED",
    "PYTHONHOME",
    "PYTHONOPTIMIZE",
    "PYTHONPATH",
    "PYTHONSAFEPATH",
)
CONFIGURATION_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
TOOL_COMMANDS: dict[str, tuple[str, tuple[str, ...] | None]] = {
    "bash": ("bash", ("--version",)),
    "dirname": ("dirname", None),
    "elan": ("elan", ("--version",)),
    "env": ("env", None),
    "find": ("find", None),
    "git": ("git", ("--version",)),
    "grep": ("grep", None),
    "lake": ("lake", ("--version",)),
    "lean": ("lean", ("--version",)),
    "python": ("python3", ("--version",)),
    "seq": ("seq", None),
    "sort": ("sort", None),
    "timeout": ("timeout", ("--version",)),
}

# These are execution roots, not hand-maintained file lists.  Their repository
# import closures are computed below.  The broad stages intentionally use every
# tracked Lean source because their commands scan/build the complete library.
STAGE_LEAN_ROOTS: dict[str, tuple[str, ...] | None] = {
    "evidence": None,
    "moderate": (
        "CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.TheoremAssembly",
    ),
    "ternary-upper": (
        "CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified",
        "CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Replay.Verified",
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Certificate",
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Certificate",
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256RescaledFrontier",
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406.Certificate",
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Certificate",
        "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Certificate",
        "CertifiedJL.Tests.UpperTailCanaries",
        "CertifiedJL.Tests.SparseUpperContourFamilyFixture",
    ),
    "library": None,
    "complete": (),  # populated from evidence/validation-roots.toml
}


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object: {path}")
    return value


def write_json_new(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2, sort_keys=True) + "\n")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def require_outside_checkout(path: Path) -> None:
    resolved = path.resolve()
    root = ROOT.resolve()
    if resolved == root or root in resolved.parents:
        raise ValueError(f"kernel execution artifacts must stay outside the checkout: {path}")


def require_new_artifact(path: Path, label: str) -> None:
    require_outside_checkout(path)
    if path.exists() or path.is_symlink():
        raise ValueError(f"{label} already exists; kernel execution artifacts are immutable: {path}")


def require_distinct_paths(paths: dict[str, Path]) -> None:
    resolved: dict[Path, str] = {}
    for label, path in paths.items():
        key = path.resolve()
        if key in resolved:
            raise ValueError(f"{label} overlaps {resolved[key]}: {path}")
        resolved[key] = label


def require_disjoint_trees(first: Path, second: Path) -> None:
    first_resolved = first.resolve()
    second_resolved = second.resolve()
    if (first_resolved == second_resolved
            or first_resolved in second_resolved.parents
            or second_resolved in first_resolved.parents):
        raise ValueError(f"kernel artifact trees must not overlap: {first}, {second}")


def receipt_digest(receipt: dict[str, Any]) -> str:
    unsigned = {key: value for key, value in receipt.items() if key != "receipt_digest"}
    return canonical_digest("CertifiedJL-kernel-stage-receipt-v1", unsigned)


def aggregate_digest(record: dict[str, Any]) -> str:
    unsigned = {key: value for key, value in record.items() if key != "execution_digest"}
    return canonical_digest("CertifiedJL-kernel-execution-record-v1", unsigned)


def selection_digest(selection: dict[str, Any]) -> str:
    unsigned = {key: value for key, value in selection.items() if key != "selection_digest"}
    return canonical_digest("CertifiedJL-kernel-stage-selection-v1", unsigned)


def make_stage_selection(
    *, stage: StagePlan, disposition: str, receipt: dict[str, Any],
    assembly_run: dict[str, str], current_identity: dict[str, Any],
) -> dict[str, Any]:
    if disposition not in {"executed", "reused"}:
        raise ValueError("invalid kernel stage disposition")
    selection: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": "kernel-stage-selection",
        "attests_execution": False,
        "assembly_run": copy.deepcopy(assembly_run),
        "assembly_source_digest": current_identity["digest"],
        "stage": {"index": stage.index, "name": stage.name, "script": stage.script},
        "disposition": disposition,
        "receipt_digest": receipt["receipt_digest"],
        "execution_run": copy.deepcopy(receipt["run"]),
    }
    selection["selection_digest"] = selection_digest(selection)
    return selection


def validate_stage_selection(
    selection: object, *, stage: StagePlan, receipt: dict[str, Any],
) -> None:
    if not isinstance(selection, dict) or set(selection) != {
        "schema_version", "record_kind", "attests_execution", "assembly_run",
        "assembly_source_digest", "stage", "disposition", "receipt_digest",
        "execution_run", "selection_digest",
    }:
        raise ValueError("invalid kernel stage selection fields")
    if (selection["schema_version"] != SCHEMA_VERSION
            or selection["record_kind"] != "kernel-stage-selection"
            or selection["attests_execution"] is not False
            or selection["disposition"] not in {"executed", "reused"}):
        raise ValueError("invalid kernel stage selection")
    run = selection["assembly_run"]
    if not isinstance(run, dict) or set(run) != {
        "repository", "workflow", "run_id", "run_attempt", "source_commit"
    } or not all(isinstance(value, str) and value for value in run.values()):
        raise ValueError("invalid kernel stage selection assembly run")
    if not isinstance(selection["assembly_source_digest"], str) or re.fullmatch(
        r"sha256:[0-9a-f]{64}", selection["assembly_source_digest"]
    ) is None:
        raise ValueError("invalid kernel stage selection source digest")
    if selection["selection_digest"] != selection_digest(selection):
        raise ValueError("invalid kernel stage selection digest")
    if selection["stage"] != {"index": stage.index, "name": stage.name, "script": stage.script}:
        raise ValueError("kernel stage selection does not follow the fixed plan")
    if (selection["receipt_digest"] != receipt["receipt_digest"]
            or selection["execution_run"] != receipt["run"]):
        raise ValueError("kernel stage selection does not bind its receipt")


def validate_source_identity(identity: dict[str, Any], commit: str) -> None:
    validate_identity_document(identity)
    if identity["mode"] != "kernel":
        raise ValueError("kernel receipt requires a kernel source identity")
    if identity["source_commit"] != commit:
        raise ValueError("source identity commit does not match workflow commit")


def parse_utc(value: object, field: str) -> datetime:
    if not isinstance(value, str) or not value.endswith("Z"):
        raise ValueError(f"invalid {field}")
    try:
        return datetime.fromisoformat(value[:-1] + "+00:00")
    except ValueError as exc:
        raise ValueError(f"invalid {field}") from exc


def command_output(
    argv: list[str], *, environ: dict[str, str] | None = None,
) -> str:
    return subprocess.check_output(
        argv, cwd=ROOT, text=True, stderr=subprocess.STDOUT, env=environ,
    ).strip()


def resolved_tool_identity(
    executable: str, version_args: tuple[str, ...] | None,
    *, search_path: str | None = None, environ: dict[str, str] | None = None,
) -> dict[str, str]:
    candidate = shutil.which(executable, path=search_path)
    if candidate is None:
        raise ValueError(f"required kernel stage tool is not on PATH: {executable}")
    invocation = Path(candidate)
    if not invocation.is_absolute():
        invocation = ROOT / invocation
    invocation = invocation.absolute()
    resolved = invocation.resolve(strict=True)
    if not resolved.is_file():
        raise ValueError(f"kernel stage tool is not a regular file: {resolved}")
    result = {
        "invocation_path": str(invocation),
        "resolved_path": str(resolved),
        "sha256": sha256_file(resolved),
    }
    if version_args is not None:
        # Preserve argv[0]'s shim basename. Elan's lean/lake multicall shims all
        # resolve to elan-init but select different programs from this basename.
        result["version"] = command_output(
            [str(invocation), *version_args], environ=environ,
        )
    return result


def selected_elan_tool_identity(
    executable: str, *, elan_invocation: str, environ: dict[str, str],
) -> dict[str, str]:
    selected_text = command_output(
        [elan_invocation, "which", executable], environ=environ,
    )
    selected = Path(selected_text)
    if not selected.is_absolute():
        selected = ROOT / selected
    resolved = selected.resolve(strict=True)
    if not resolved.is_file():
        raise ValueError(f"selected Elan tool is not a regular file: {resolved}")
    return {"path": str(resolved), "sha256": sha256_file(resolved)}


def dependency_manifest(root: Path = ROOT) -> list[dict[str, Any]]:
    manifest = read_json(root / "lake-manifest.json")
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise ValueError("lake-manifest.json has no package list")
    result = []
    for package in packages:
        if not isinstance(package, dict) or not isinstance(package.get("name"), str):
            raise ValueError("lake-manifest.json has an invalid package entry")
        result.append({
            key: package.get(key)
            for key in ("name", "type", "scope", "url", "rev", "subDir")
            if key in package
        })
    names = [package["name"] for package in result]
    if len(names) != len(set(names)):
        raise ValueError("lake-manifest.json has duplicate package names")
    return sorted(result, key=lambda package: package["name"])


def source_execution_context(root: Path = ROOT) -> dict[str, Any]:
    return {
        "configuration_sha256": {
            relative: sha256_file(root / relative) for relative in CONFIGURATION_FILES
        },
        "dependencies": dependency_manifest(root),
    }


def _script_closure(stage: StagePlan, tracked: set[Path], root: Path) -> set[Path]:
    """Return the conservative shared procedure closure.

    Python imports and shell dispatch are not reliably discoverable from text,
    so every tracked file under scripts/ is bound to every stage.
    """
    del stage
    scripts = {
        path for path in tracked
        if path.relative_to(root).parts[:1] == ("scripts",)
    }
    if any(not path.is_file() or path.is_symlink() for path in scripts):
        raise ValueError("kernel stage scripts must be tracked regular files")
    return scripts


def _validation_group_roots(root: Path, group: str) -> tuple[str, ...]:
    with (root / "evidence/validation-roots.toml").open("rb") as stream:
        document = tomllib.load(stream)
    for record in document.get("lean_group", []):
        if record.get("id") == group:
            roots = record.get("roots")
            if not isinstance(roots, list) or not all(isinstance(item, str) for item in roots):
                raise ValueError(f"invalid validation root group: {group}")
            return tuple(roots)
    raise ValueError(f"missing validation root group: {group}")


def require_no_ignored_stage_sources(root: Path = ROOT) -> None:
    """Reject ignored files under repository source/validator scan roots."""
    payload = subprocess.check_output(
        [
            "git", "ls-files", "-z", "--others", "--ignored",
            "--exclude-standard", "--", "CertifiedJL", "CertifiedJLFast",
            "Vendor", "scripts", "evidence", "docs", ".github",
        ],
        cwd=root,
    )
    ignored = []
    for part in payload.split(b"\0"):
        if not part:
            continue
        relative = part.decode("utf-8")
        path = Path(relative)
        # The runner starts before repository-local imports with bytecode writes
        # disabled and a fresh, nonexistent external cache prefix. Child Python
        # processes inherit that policy, so source-tree caches cannot be read or
        # written and are not stage inputs. Other ignored files remain fatal.
        if "__pycache__" in path.parts or path.suffix == ".pyc":
            continue
        ignored.append(relative)
    ignored.sort()
    if ignored:
        raise ValueError(f"kernel stage inputs contain ignored source files: {ignored}")


def require_regular_stage_inputs(inputs: set[Path], root: Path = ROOT) -> None:
    for path in inputs:
        if path.is_symlink() or not path.is_file():
            raise ValueError(
                f"kernel stage input must be a tracked regular file: {path.relative_to(root)}"
            )


def stage_input_paths(
    stage: StagePlan, *, root: Path = ROOT, tracked: set[Path] | None = None,
    graph: dict[str, tuple[str, ...]] | None = None,
) -> set[Path]:
    """Return a sound tracked input overapproximation for one fixed stage."""
    tracked_set = tracked_sources() if tracked is None else tracked
    scripts = _script_closure(stage, tracked_set, root)
    import_dependencies = import_graph(tracked_set) if graph is None else graph
    roots = STAGE_LEAN_ROOTS[stage.name]
    if roots is None:
        lean_files = {path for path in tracked_set if path.suffix == ".lean"}
    else:
        if stage.name == "complete":
            roots = _validation_group_roots(root, "kernel-canaries")
        modules = closure(import_dependencies, set(roots))
        require_tracked_closure(modules, set(roots), tracked_set, root)
        lean_files = {
            module_source(module) if root == ROOT
            else root / (module.replace(".", "/") + ".lean")
            for module in modules
        } & tracked_set

    if stage.name == "evidence":
        inputs = set(tracked_set)
    else:
        inputs = scripts | lean_files | {
            path for path in tracked_set
            if path.suffix != ".lean" and path.relative_to(root).parts[:1] != ("paper",)
        }
    # Catalog/topology inputs are consumed indirectly by the evidence and
    # library dispatchers; validation roots schedule the final canaries.
    supplement = {
        "evidence": ("evidence", ".github/workflows", "paper", "docs", "Makefile"),
        "moderate": (),
        "ternary-upper": ("evidence/certificates/replay-families.toml", "evidence/certificates/public-results.toml", "paper/experiments/sparse-upper-centered-hybrid", "paper/artifact/upper-gap/verify_U338.py", "CertifiedJL/Tests/Generated/SparseUpperContourFamilyFixture", "CertifiedJL/Certificates/Families/L2Upper/Rows512Bits192/ShortTail/Replay", "CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay"),
        "library": ("evidence/validation-roots.toml", "evidence/certificates/replay-families.toml", "evidence/certificates/public-results.toml"),
        "complete": ("evidence/validation-roots.toml",),
    }[stage.name]
    for path in tracked_set:
        relative = path.relative_to(root).as_posix()
        if any(relative == prefix or relative.startswith(prefix + "/") for prefix in supplement):
            inputs.add(path)
    require_regular_stage_inputs(inputs, root)
    return inputs


def compute_stage_identities(root: Path = ROOT) -> dict[str, dict[str, Any]]:
    """Snapshot deterministic stage-scoped identities from a clean checkout."""
    require_clean_source()
    require_no_ignored_stage_sources(root)
    tracked = tracked_sources()
    graph = import_graph(tracked)
    result: dict[str, dict[str, Any]] = {}
    for stage in STAGE_PLAN:
        inputs = stage_input_paths(stage, root=root, tracked=tracked, graph=graph)
        result[stage.name] = stage_identity_from_paths(stage, inputs, root=root)
    require_clean_source()
    return result


def stage_identity_from_paths(
    stage: StagePlan, inputs: set[Path], *, root: Path = ROOT,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "stage": {"index": stage.index, "name": stage.name, "script": stage.script},
        "input_count": len(inputs),
        "inputs_digest": "sha256:" + digest_files(
            b"CertifiedJL-kernel-stage-input-files-v1", inputs, root
        ),
    }
    record["digest"] = canonical_digest("CertifiedJL-kernel-stage-inputs-v1", record)
    return record


def validate_stage_identity(identity: object, stage: StagePlan) -> None:
    if not isinstance(identity, dict) or set(identity) != {
        "stage", "input_count", "inputs_digest", "digest"
    }:
        raise ValueError("invalid kernel stage input identity")
    if identity["stage"] != {"index": stage.index, "name": stage.name, "script": stage.script}:
        raise ValueError("kernel stage input identity has the wrong stage")
    if type(identity["input_count"]) is not int or identity["input_count"] < 1:
        raise ValueError("invalid kernel stage input count")
    if not isinstance(identity["inputs_digest"], str) or re.fullmatch(
        r"sha256:[0-9a-f]{64}", identity["inputs_digest"]
    ) is None:
        raise ValueError("invalid kernel stage inputs digest")
    unsigned = {key: value for key, value in identity.items() if key != "digest"}
    if identity["digest"] != canonical_digest("CertifiedJL-kernel-stage-inputs-v1", unsigned):
        raise ValueError("invalid kernel stage identity digest")


def collect_stage_context(
    *, runner_os: str, runner_arch: str, environ: dict[str, str] | None = None,
) -> dict[str, Any]:
    env = os.environ if environ is None else environ
    environment = {key: env.get(key, "") for key in REPLAY_ENV_KEYS}
    environment["PATH"] = env["PATH"] if "PATH" in env else os.defpath
    environment["LEAN_NUM_THREADS"] = (
        env.get("LEAN_NUM_THREADS") or DEFAULT_LEAN_NUM_THREADS
    )
    environment["LEAN_GC_THRESHOLD"] = (
        env.get("LEAN_GC_THRESHOLD") or DEFAULT_LEAN_GC_THRESHOLD
    )
    tools = {
        name: resolved_tool_identity(
            executable, version_args, search_path=environment["PATH"], environ=env,
        )
        for name, (executable, version_args) in TOOL_COMMANDS.items()
    }
    for executable in ("lean", "lake"):
        tools[executable]["selected_toolchain"] = selected_elan_tool_identity(
            executable,
            elan_invocation=tools["elan"]["invocation_path"],
            environ=env,
        )
    return {
        **source_execution_context(ROOT),
        "environment": environment,
        "runner": {"os": runner_os, "arch": runner_arch},
        "verified_dependencies": list(verified_dependencies(ROOT)),
        "tools": tools,
    }


def expected_stage(name: str, index: int, script: str, timeout_minutes: int) -> StagePlan:
    if (not isinstance(name, str) or type(index) is not int
            or not isinstance(script, str) or type(timeout_minutes) is not int):
        raise ValueError("stage descriptor has invalid field types")
    stage = PLAN_BY_NAME.get(name)
    if stage is None or (stage.index, stage.script, stage.timeout_minutes) != (
        index,
        script,
        timeout_minutes,
    ):
        raise ValueError("stage does not match the fixed kernel replay plan")
    return stage


def validate_cache_record(cache: object) -> None:
    if not isinstance(cache, dict) or set(cache) != {
        "policy", "requested_key", "restored_key"
    }:
        raise ValueError("invalid kernel stage cache provenance")
    if not all(isinstance(cache[key], str) for key in cache):
        raise ValueError("kernel stage cache provenance values must be strings")
    policy = cache["policy"]
    requested = cache["requested_key"]
    restored = cache["restored_key"]
    if policy == "github-actions-kernel":
        if not requested.startswith(KERNEL_CACHE_PREFIX):
            raise ValueError("kernel CI requested cache key is outside its namespace")
        if restored and not restored.startswith(KERNEL_CACHE_PREFIX):
            raise ValueError("kernel CI restored cache key is outside its namespace")
    elif policy == "local-project-cache":
        if requested != "local:.lake/build" or restored not in {
            "", "local:.lake/build"
        }:
            raise ValueError("invalid local project cache provenance")
    else:
        raise ValueError("unknown kernel stage cache policy")


def validate_stage_receipt(receipt: dict[str, Any], log_path: Path) -> None:
    required = {
        "schema_version", "record_kind", "attests_execution", "success",
        "source_identity", "run", "stage", "stage_identity", "execution", "context", "cache",
        "previous_receipt_digest", "receipt_digest",
    }
    if set(receipt) != required:
        raise ValueError("unexpected kernel stage receipt fields")
    if (type(receipt["schema_version"]) is not int
            or receipt["schema_version"] != SCHEMA_VERSION
            or receipt["record_kind"] != "kernel-stage-execution"
            or receipt["attests_execution"] is not True):
        raise ValueError("invalid kernel stage receipt header")
    if receipt["receipt_digest"] != receipt_digest(receipt):
        raise ValueError("invalid kernel stage receipt digest")

    run = receipt["run"]
    if not isinstance(run, dict) or set(run) != {
        "repository", "workflow", "run_id", "run_attempt", "source_commit"
    }:
        raise ValueError("invalid kernel stage run identity")
    if not all(isinstance(run[key], str) and run[key] for key in run):
        raise ValueError("kernel stage run identity values must be nonempty strings")
    validate_source_identity(receipt["source_identity"], run["source_commit"])

    stage_record = receipt["stage"]
    if not isinstance(stage_record, dict) or set(stage_record) != {
        "index", "name", "script"
    }:
        raise ValueError("invalid kernel stage descriptor")
    stage = expected_stage(
        stage_record["name"], stage_record["index"], stage_record["script"],
        receipt["execution"].get("timeout_minutes")
        if isinstance(receipt["execution"], dict) else -1,
    )
    validate_stage_identity(receipt["stage_identity"], stage)

    execution = receipt["execution"]
    if not isinstance(execution, dict) or set(execution) != {
        "command", "timeout_minutes", "started_utc", "finished_utc",
        "exit_code", "log",
    }:
        raise ValueError("invalid kernel stage execution")
    if type(execution["timeout_minutes"]) is not int:
        raise ValueError("kernel stage timeout must be an integer")
    if execution["command"] != stage.command:
        raise ValueError("kernel stage command does not match the fixed replay plan")
    if type(execution["exit_code"]) is not int:
        raise ValueError("kernel stage exit code must be an integer")
    if receipt["success"] is not (execution["exit_code"] == 0):
        raise ValueError("kernel stage success does not match its exit code")
    if parse_utc(execution["finished_utc"], "finished_utc") < parse_utc(
        execution["started_utc"], "started_utc"
    ):
        raise ValueError("kernel stage finished before it started")
    log = execution["log"]
    if not isinstance(log, dict) or set(log) != {"name", "sha256", "size_bytes"}:
        raise ValueError("invalid kernel stage log descriptor")
    if (log["name"] != LOG_NAME or type(log["size_bytes"]) is not int
            or log["size_bytes"] < 0):
        raise ValueError("invalid kernel stage log metadata")
    if (log_path.is_symlink() or not log_path.is_file()
            or log_path.stat().st_size != log["size_bytes"]):
        raise ValueError("kernel stage log is missing or has the wrong size")
    if sha256_file(log_path) != log["sha256"]:
        raise ValueError("kernel stage log hash mismatch")

    context = receipt["context"]
    if not isinstance(context, dict) or set(context) != {
        "configuration_sha256", "dependencies", "environment", "runner", "tools",
        "verified_dependencies",
    }:
        raise ValueError("invalid kernel stage execution context")
    if not isinstance(context["environment"], dict) or set(context["environment"]) != set(REPLAY_ENV_KEYS):
        raise ValueError("invalid kernel stage replay environment")
    if not all(isinstance(value, str) for value in context["environment"].values()):
        raise ValueError("kernel stage replay environment values must be strings")
    if not isinstance(context["runner"], dict) or set(context["runner"]) != {"os", "arch"}:
        raise ValueError("invalid kernel stage runner identity")
    if not isinstance(context["tools"], dict) or set(context["tools"]) != set(TOOL_COMMANDS):
        raise ValueError("invalid kernel stage tool identity")
    if not all(isinstance(value, str) and value for value in context["runner"].values()):
        raise ValueError("kernel stage runner identity values must be nonempty strings")
    for name, value in context["tools"].items():
        expected_fields = {"invocation_path", "resolved_path", "sha256"}
        if TOOL_COMMANDS[name][1] is not None:
            expected_fields.add("version")
        if name in {"lean", "lake"}:
            expected_fields.add("selected_toolchain")
        if (not isinstance(value, dict)
                or set(value) != expected_fields
                or not all(
                    isinstance(item, str) and item
                    for key, item in value.items() if key != "selected_toolchain"
                )
                or re.fullmatch(r"sha256:[0-9a-f]{64}", value["sha256"]) is None):
            raise ValueError("invalid resolved kernel stage tool identity")
        selected = value.get("selected_toolchain")
        if selected is not None and (
            not isinstance(selected, dict) or set(selected) != {"path", "sha256"}
            or not all(isinstance(item, str) and item for item in selected.values())
            or re.fullmatch(r"sha256:[0-9a-f]{64}", selected["sha256"]) is None
        ):
            raise ValueError("invalid selected Elan tool identity")
    manifest_by_name = {entry["name"]: entry for entry in context["dependencies"]}
    observed = context["verified_dependencies"]
    if not isinstance(observed, list) or len(observed) != len(manifest_by_name):
        raise ValueError("invalid verified kernel dependency list")
    observed_names: list[str] = []
    for dependency in observed:
        if not isinstance(dependency, dict) or set(dependency) != {
            "name", "type", "expected_url", "actual_url", "expected_revision",
            "actual_revision", "status_sha256",
        }:
            raise ValueError("invalid verified kernel dependency record")
        if not all(isinstance(dependency[key], str) for key in dependency):
            raise ValueError("verified kernel dependency values must be strings")
        observed_names.append(dependency["name"])
        declared = manifest_by_name.get(dependency["name"])
        if (declared is None or declared.get("type") != "git"
                or dependency["type"] != "git"
                or dependency["expected_url"] != declared.get("url")
                or dependency["actual_url"] != declared.get("url")
                or dependency["expected_revision"] != declared.get("rev")
                or dependency["actual_revision"] != declared.get("rev")
                or dependency["status_sha256"] != hashlib.sha256(b"").hexdigest()):
            raise ValueError("verified kernel dependency does not match its manifest")
    if len(observed_names) != len(set(observed_names)):
        raise ValueError("verified kernel dependency names must be unique")
    if set(observed_names) != set(manifest_by_name):
        raise ValueError("verified kernel dependencies do not cover the exact manifest")
    validate_cache_record(receipt["cache"])


def validate_predecessor(
    *, stage: StagePlan, receipt: dict[str, Any] | None, log_path: Path | None,
    context: dict[str, Any],
) -> str | None:
    if stage.index == 0:
        if receipt is not None or log_path is not None:
            raise ValueError("first kernel stage must not have a predecessor receipt")
        return None
    if receipt is None or log_path is None:
        raise ValueError("kernel stage is missing its predecessor receipt")
    validate_stage_receipt(receipt, log_path)
    previous_stage = STAGE_PLAN[stage.index - 1]
    if receipt["stage"] != {
        "index": previous_stage.index,
        "name": previous_stage.name,
        "script": previous_stage.script,
    }:
        raise ValueError("kernel stage predecessor is not the immediately prior stage")
    if not receipt["success"]:
        raise ValueError("kernel stage predecessor was not successful")
    if receipt["context"] != context:
        raise ValueError("kernel stage predecessor has a different execution context")
    return receipt["receipt_digest"]


def create_stage_receipt(
    *, identity_before: dict[str, Any], identity_after: dict[str, Any],
    repository: str, workflow: str, run_id: str, run_attempt: str, commit: str,
    name: str, index: int, script: str, timeout_minutes: int,
    started_utc: str, finished_utc: str, exit_code: int, log_path: Path,
    context: dict[str, Any], cache: dict[str, str],
    stage_identity: dict[str, Any],
    previous_receipt: dict[str, Any] | None = None,
    previous_log: Path | None = None,
) -> dict[str, Any]:
    validate_source_identity(identity_before, commit)
    validate_source_identity(identity_after, commit)
    if identity_before != identity_after:
        raise ValueError("source identity changed during kernel replay stage")
    stage = expected_stage(name, index, script, timeout_minutes)
    run = {
        "repository": repository,
        "workflow": workflow,
        "run_id": run_id,
        "run_attempt": run_attempt,
        "source_commit": commit,
    }
    validate_stage_identity(stage_identity, stage)
    previous_digest = validate_predecessor(
        stage=stage,
        receipt=previous_receipt,
        log_path=previous_log,
        context=context,
    )

    if not log_path.is_file():
        raise ValueError("kernel stage log does not exist")
    receipt: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": "kernel-stage-execution",
        "attests_execution": True,
        "success": exit_code == 0,
        "source_identity": copy.deepcopy(identity_before),
        "run": run,
        "stage": {"index": stage.index, "name": stage.name, "script": stage.script},
        "stage_identity": copy.deepcopy(stage_identity),
        "execution": {
            "command": stage.command,
            "timeout_minutes": stage.timeout_minutes,
            "started_utc": started_utc,
            "finished_utc": finished_utc,
            "exit_code": exit_code,
            "log": {
                "name": LOG_NAME,
                "sha256": sha256_file(log_path),
                "size_bytes": log_path.stat().st_size,
            },
        },
        "context": copy.deepcopy(context),
        "cache": copy.deepcopy(cache),
        "previous_receipt_digest": previous_digest,
    }
    receipt["receipt_digest"] = receipt_digest(receipt)
    validate_stage_receipt(receipt, log_path)
    return receipt


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def run_and_stream(
    command: list[str], *, cwd: Path, log_path: Path,
    output: BinaryIO | None = None,
) -> int:
    """Run one command, tee its complete byte stream, and return its exit code."""
    destination = sys.stdout.buffer if output is None else output
    log_path.parent.mkdir(parents=True, exist_ok=True)
    process: subprocess.Popen[bytes] | None = None
    try:
        with log_path.open("xb") as log:
            process = subprocess.Popen(
                command,
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            if process.stdout is None:  # pragma: no cover - guaranteed by PIPE
                raise RuntimeError("kernel stage log pipe was not created")
            with process.stdout:
                for chunk in iter(process.stdout.readline, b""):
                    log.write(chunk)
                    log.flush()
                    destination.write(chunk)
                    destination.flush()
            return process.wait()
    except BaseException:
        if process is not None:
            terminate_process_group(process)
        raise


def terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    """Stop and reap a stage process and every descendant in its new session."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        process.wait()
        return
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        pass
    deadline = time.monotonic() + 10
    while time.monotonic() < deadline:
        try:
            os.killpg(process.pid, 0)
        except ProcessLookupError:
            return
        time.sleep(0.1)
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    process.wait()


def run_fixed_stage(
    *, repository: str, workflow: str, run_id: str, run_attempt: str,
    commit: str, name: str, index: int, script: str, timeout_minutes: int,
    log_path: Path, output: Path, runner_os: str, runner_arch: str,
    cache_policy: str, cache_requested_key: str, cache_restored_key: str,
    previous_receipt_path: Path | None = None,
    expected_stage_identity: dict[str, Any] | None = None,
) -> int:
    """Run one fixed stage, stream its log, and seal the observed result."""
    require_new_artifact(log_path, "kernel stage log")
    require_new_artifact(output, "kernel stage receipt")
    path_set = {"kernel stage log": log_path, "kernel stage receipt": output}
    if previous_receipt_path is not None:
        require_outside_checkout(previous_receipt_path)
        previous_log_path = previous_receipt_path.with_name(LOG_NAME)
        require_outside_checkout(previous_log_path)
        path_set.update({
            "predecessor receipt": previous_receipt_path,
            "predecessor log": previous_log_path,
        })
    require_distinct_paths(path_set)
    stage = expected_stage(name, index, script, timeout_minutes)
    identity_before = compute_kernel_identity()
    validate_source_identity(identity_before, commit)
    context = collect_stage_context(runner_os=runner_os, runner_arch=runner_arch)
    if previous_receipt_path is not None and previous_receipt_path.is_symlink():
        raise ValueError("kernel stage predecessor receipt must not be a symlink")
    previous_receipt = (
        read_json(previous_receipt_path) if previous_receipt_path is not None else None
    )
    previous_log = (
        previous_receipt_path.with_name(LOG_NAME)
        if previous_receipt_path is not None else None
    )
    cache = {
        "policy": cache_policy,
        "requested_key": cache_requested_key,
        "restored_key": cache_restored_key,
    }
    validate_cache_record(cache)
    validate_predecessor(
        stage=stage,
        receipt=previous_receipt,
        log_path=previous_log,
        context=context,
    )
    stage_identity = (
        compute_stage_identities()[stage.name]
        if expected_stage_identity is None else expected_stage_identity
    )
    validate_stage_identity(stage_identity, stage)

    started = utc_now()
    exit_code = run_and_stream(stage.command, cwd=ROOT, log_path=log_path)
    finished = utc_now()

    identity_after = compute_kernel_identity()
    context_after = collect_stage_context(runner_os=runner_os, runner_arch=runner_arch)
    if context_after != context:
        raise ValueError("execution context changed during kernel replay stage")
    receipt = create_stage_receipt(
        identity_before=identity_before,
        identity_after=identity_after,
        repository=repository,
        workflow=workflow,
        run_id=run_id,
        run_attempt=run_attempt,
        commit=commit,
        name=stage.name,
        index=stage.index,
        script=stage.script,
        timeout_minutes=stage.timeout_minutes,
        started_utc=started,
        finished_utc=finished,
        exit_code=exit_code,
        log_path=log_path,
        context=context,
        cache=cache,
        stage_identity=stage_identity,
        previous_receipt=previous_receipt,
        previous_log=previous_log,
    )
    write_json_new(output, receipt)
    return exit_code


def verify_run(
    *, receipts: list[tuple[dict[str, Any], Path]],
    current_identity: dict[str, Any], repository: str, workflow: str,
    run_id: str, run_attempt: str, commit: str,
    current_stage_identities: dict[str, dict[str, Any]],
    current_context: dict[str, Any],
    dispositions: dict[str, str] | None = None,
) -> dict[str, Any]:
    validate_source_identity(current_identity, commit)
    if len(receipts) != len(STAGE_PLAN):
        raise ValueError("kernel proof record requires exactly five stage receipts")
    for receipt, log_path in receipts:
        validate_stage_receipt(receipt, log_path)
    ordered = sorted(receipts, key=lambda item: item[0]["stage"]["index"])
    indices = [receipt["stage"]["index"] for receipt, _ in ordered]
    if indices != list(range(len(STAGE_PLAN))):
        raise ValueError("kernel stage receipts are missing, duplicated, or out of order")
    assembly_run = {
        "repository": repository,
        "workflow": workflow,
        "run_id": run_id,
        "run_attempt": run_attempt,
        "source_commit": commit,
    }
    stage_receipts = []
    selections = []
    previous_selected_digest: str | None = None
    dispositions = dispositions or {stage.name: "executed" for stage in STAGE_PLAN}
    if set(dispositions) != set(PLAN_BY_NAME) or any(
        value not in {"executed", "reused"} for value in dispositions.values()
    ):
        raise ValueError("invalid kernel stage selection dispositions")
    for stage, (receipt, _) in zip(STAGE_PLAN, ordered, strict=True):
        if receipt["stage"] != {
            "index": stage.index, "name": stage.name, "script": stage.script
        }:
            raise ValueError("kernel stage receipt does not match the fixed replay plan")
        if receipt["stage_identity"] != current_stage_identities.get(stage.name):
            raise ValueError(f"kernel stage inputs do not match this checkout: {stage.name}")
        if receipt["context"] != current_context:
            raise ValueError(f"kernel stage execution context does not match: {stage.name}")
        if not receipt["success"] or receipt["execution"]["exit_code"] != 0:
            raise ValueError("kernel proof record contains a failed stage")
        disposition = dispositions[stage.name]
        if disposition == "executed" and receipt["run"] != assembly_run:
            raise ValueError("executed kernel stage does not belong to the assembly run")
        if (disposition == "executed"
                and receipt["previous_receipt_digest"] != previous_selected_digest):
            raise ValueError("executed kernel stage predecessor digest chain is broken")
        stage_receipts.append(receipt)
        selections.append({
            "index": stage.index,
            "name": stage.name,
            "disposition": disposition,
            "stage_identity_digest": receipt["stage_identity"]["digest"],
            "receipt_digest": receipt["receipt_digest"],
            "execution_run": copy.deepcopy(receipt["run"]),
            "execution_source_digest": receipt["source_identity"]["digest"],
        })
        previous_selected_digest = receipt["receipt_digest"]

    record: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": "kernel-proof-execution",
        "attests_execution": True,
        "success": True,
        "source_identity": current_identity,
        "assembly_run": assembly_run,
        "context": copy.deepcopy(current_context),
        "stage_selections": selections,
        "stage_receipts": stage_receipts,
    }
    record["execution_digest"] = aggregate_digest(record)
    return record


def compute_kernel_identity() -> dict[str, Any]:
    # Imported lazily so pure receipt tests can use fixture identities cheaply.
    from compute_replay_digest import compute_identity

    return compute_identity(mode="kernel")


def run_stage_cli(args: argparse.Namespace) -> int:
    require_python_cache_isolation()
    return run_fixed_stage(
        repository=args.repository,
        workflow=args.workflow,
        run_id=args.run_id,
        run_attempt=args.run_attempt,
        commit=args.commit,
        name=args.family,
        index=args.stage_index,
        script=args.script,
        timeout_minutes=args.timeout_minutes,
        log_path=args.log,
        output=args.output,
        runner_os=args.runner_os,
        runner_arch=args.runner_arch,
        cache_policy=args.cache_policy,
        cache_requested_key=args.cache_requested_key,
        cache_restored_key=args.cache_restored_key,
        previous_receipt_path=args.previous_receipt,
    )


def load_execution_receipt_tree(
    receipts_dir: Path, *, run_id: str, run_attempt: str,
) -> list[tuple[dict[str, Any], Path]]:
    if receipts_dir.is_symlink() or not receipts_dir.is_dir():
        raise ValueError("kernel receipt tree must be a non-symlinked directory")
    expected_names = {
        f"kernel-proof-stage-{run_id}-{run_attempt}-{stage.name}": stage
        for stage in STAGE_PLAN
    }
    entries = list(receipts_dir.iterdir())
    if {entry.name for entry in entries} != set(expected_names):
        raise ValueError("kernel receipt tree has extra or missing stage directories")
    receipts: list[tuple[dict[str, Any], Path]] = []
    for name, stage in expected_names.items():
        directory = receipts_dir / name
        if directory.is_symlink() or not directory.is_dir():
            raise ValueError(f"kernel receipt stage is not a regular directory: {name}")
        if {entry.name for entry in directory.iterdir()} != {RECEIPT_NAME, LOG_NAME}:
            raise ValueError(f"kernel receipt stage has extra or missing files: {stage.name}")
        receipt_path = directory / RECEIPT_NAME
        log_path = directory / LOG_NAME
        if receipt_path.is_symlink() or log_path.is_symlink():
            raise ValueError("kernel receipt artifacts must not be symlinks")
        receipts.append((read_json(receipt_path), log_path))
    return receipts


def verify_run_cli(args: argparse.Namespace) -> None:
    require_python_cache_isolation()
    require_outside_checkout(args.identity)
    require_outside_checkout(args.receipts_dir)
    require_new_artifact(args.output, "kernel proof execution record")
    supplied_identity = read_json(args.identity)
    current_identity = compute_kernel_identity()
    validate_source_identity(current_identity, args.commit)
    if supplied_identity != current_identity:
        raise ValueError("supplied source identity does not match the current checkout")
    receipts = load_execution_receipt_tree(
        args.receipts_dir, run_id=args.run_id, run_attempt=args.run_attempt,
    )
    stage_identities = compute_stage_identities()
    runner = receipts[0][0]["context"]["runner"] if receipts else {"os": "", "arch": ""}
    context = collect_stage_context(runner_os=runner["os"], runner_arch=runner["arch"])
    record = verify_run(
        receipts=receipts,
        current_identity=current_identity,
        repository=args.repository,
        workflow=args.workflow,
        run_id=args.run_id,
        run_attempt=args.run_attempt,
        commit=args.commit,
        current_stage_identities=stage_identities,
        current_context=context,
    )
    write_json_new(args.output, record)


def git_head() -> str:
    return command_output(["git", "rev-parse", "HEAD"])


def _regular_file_bytes(path: Path) -> bytes:
    if path.is_symlink():
        raise ValueError(f"reuse artifact must not be a symlink: {path}")
    try:
        mode = path.stat().st_mode
    except FileNotFoundError as exc:
        raise ValueError(f"reuse artifact is missing: {path}") from exc
    if not stat.S_ISREG(mode):
        raise ValueError(f"reuse artifact must be a regular file: {path}")
    return path.read_bytes()


def _copy_reuse_pair(
    source_dir: Path, destination_dir: Path, *, expected_receipt_digest: str,
) -> None:
    receipt_bytes = _regular_file_bytes(source_dir / RECEIPT_NAME)
    log_bytes = _regular_file_bytes(source_dir / LOG_NAME)
    receipt = json.loads(receipt_bytes)
    if not isinstance(receipt, dict):
        raise ValueError("reuse receipt must be a JSON object")
    if (receipt.get("receipt_digest") != expected_receipt_digest
            or receipt_digest(receipt) != expected_receipt_digest):
        raise ValueError("reuse receipt changed while it was copied")
    expected_log = receipt["execution"]["log"]
    if len(log_bytes) != expected_log["size_bytes"] or (
        "sha256:" + hashlib.sha256(log_bytes).hexdigest() != expected_log["sha256"]
    ):
        raise ValueError("reuse log changed while it was copied")
    destination_dir.mkdir()
    with (destination_dir / RECEIPT_NAME).open("xb") as stream:
        stream.write(receipt_bytes)
    with (destination_dir / LOG_NAME).open("xb") as stream:
        stream.write(log_bytes)


def load_reuse_candidates(
    reuse_dir: Path, *, stage_identities: dict[str, dict[str, Any]],
    context: dict[str, Any],
) -> dict[str, tuple[dict[str, Any], Path]]:
    """Validate a canonical complete or failed-prefix run-all directory."""
    require_outside_checkout(reuse_dir)
    if reuse_dir.is_symlink() or not reuse_dir.is_dir():
        raise ValueError("reuse source must be a non-symlinked run-all directory")
    allowed_files = {SOURCE_IDENTITY_NAME, EXECUTION_RECORD_NAME}
    entries = list(reuse_dir.iterdir())
    candidates: dict[str, tuple[dict[str, Any], Path]] = {}
    bundle_receipts: list[dict[str, Any]] = []
    bundle_selections: list[dict[str, Any]] = []
    expected_next = 0
    assembly_run: dict[str, Any] | None = None
    assembly_source_digest: str | None = None
    previous_selected_digest: str | None = None
    bundle_context: dict[str, Any] | None = None
    failed_stage_seen = False
    for entry in entries:
        if entry.name in allowed_files:
            if entry.is_symlink() or not entry.is_file():
                raise ValueError(f"invalid reuse bundle artifact: {entry.name}")
            continue
        match = re.fullmatch(r"([0-4])-([a-z-]+)", entry.name)
        if match is None:
            raise ValueError(f"unexpected reuse bundle entry: {entry.name}")
    for stage in STAGE_PLAN:
        stage_dir = reuse_dir / f"{stage.index}-{stage.name}"
        if not stage_dir.exists():
            break
        if stage.index != expected_next or stage_dir.is_symlink() or not stage_dir.is_dir():
            raise ValueError("reuse stage directories must be a canonical prefix")
        if {item.name for item in stage_dir.iterdir()} != {RECEIPT_NAME, LOG_NAME, SELECTION_NAME}:
            raise ValueError(f"reuse stage directory has extra or missing files: {stage.name}")
        receipt_path = stage_dir / RECEIPT_NAME
        log_path = stage_dir / LOG_NAME
        for artifact in (receipt_path, log_path, stage_dir / SELECTION_NAME):
            _regular_file_bytes(artifact)
        receipt = read_json(receipt_path)
        validate_stage_receipt(receipt, log_path)
        selection = read_json(stage_dir / SELECTION_NAME)
        validate_stage_selection(selection, stage=stage, receipt=receipt)
        if failed_stage_seen:
            raise ValueError("reuse bundle contains a stage after its first failure")
        failed_stage_seen = not receipt["success"]
        bundle_receipts.append(receipt)
        bundle_selections.append(selection)
        if receipt["stage"] != {"index": stage.index, "name": stage.name, "script": stage.script}:
            raise ValueError("reuse receipt does not follow the fixed stage plan")
        if assembly_run is None:
            assembly_run = selection["assembly_run"]
            assembly_source_digest = selection["assembly_source_digest"]
        elif selection["assembly_run"] != assembly_run:
            raise ValueError("reuse bundle has mixed assembly run provenance")
        elif selection["assembly_source_digest"] != assembly_source_digest:
            raise ValueError("reuse bundle has mixed assembly source provenance")
        if bundle_context is None:
            bundle_context = receipt["context"]
        elif receipt["context"] != bundle_context:
            raise ValueError("reuse bundle has mixed execution contexts")
        if selection["disposition"] == "executed":
            if receipt["run"] != assembly_run:
                raise ValueError("executed reuse stage has inconsistent run provenance")
            if receipt["previous_receipt_digest"] != previous_selected_digest:
                raise ValueError("reuse bundle historical predecessor chain is broken")
        previous_selected_digest = receipt["receipt_digest"]
        expected_next += 1
        if (receipt["success"] and receipt["stage_identity"] == stage_identities[stage.name]
                and receipt["context"] == context):
            candidates[stage.name] = (receipt, receipt_path)
    present_stage_dirs = [entry for entry in entries if re.fullmatch(r"[0-4]-[a-z-]+", entry.name)]
    if len(present_stage_dirs) != expected_next:
        raise ValueError("reuse stage directories must be a canonical prefix")
    record_path = reuse_dir / EXECUTION_RECORD_NAME
    identity_path = reuse_dir / SOURCE_IDENTITY_NAME
    if record_path.exists() != identity_path.exists():
        raise ValueError("complete reuse bundle must contain both final records")
    if record_path.exists():
        _regular_file_bytes(record_path)
        _regular_file_bytes(identity_path)
        if expected_next != len(STAGE_PLAN):
            raise ValueError("completed reuse bundle is missing stage directories")
        record = read_json(record_path)
        if set(record) != {
            "schema_version", "record_kind", "attests_execution", "success",
            "source_identity", "assembly_run", "context", "stage_selections",
            "stage_receipts", "execution_digest",
        } or (record["schema_version"] != SCHEMA_VERSION
              or record["record_kind"] != "kernel-proof-execution"
              or record["attests_execution"] is not True
              or record["success"] is not True):
            raise ValueError("invalid prior kernel proof record")
        if record.get("execution_digest") != aggregate_digest(record):
            raise ValueError("invalid prior kernel proof record digest")
        if record["stage_receipts"] != bundle_receipts:
            raise ValueError("prior proof record does not bind its stage receipts")
        if record["assembly_run"] != assembly_run:
            raise ValueError("prior proof record has different assembly provenance")
        if record["context"] != bundle_context:
            raise ValueError("prior proof record has different execution context")
        expected_selections = [{
            "index": stage.index,
            "name": stage.name,
            "disposition": selection["disposition"],
            "stage_identity_digest": receipt["stage_identity"]["digest"],
            "receipt_digest": receipt["receipt_digest"],
            "execution_run": receipt["run"],
            "execution_source_digest": receipt["source_identity"]["digest"],
        } for stage, selection, receipt in zip(
            STAGE_PLAN, bundle_selections, bundle_receipts, strict=True
        )]
        if record["stage_selections"] != expected_selections:
            raise ValueError("prior proof record does not bind its stage selections")
        supplied_identity = read_json(identity_path)
        if supplied_identity != record["source_identity"]:
            raise ValueError("prior proof record source identity mismatch")
        validate_source_identity(supplied_identity, assembly_run["source_commit"])
        if supplied_identity["digest"] != assembly_source_digest:
            raise ValueError("prior stage selections bind a different assembly source")
    return candidates


def run_all_cli(args: argparse.Namespace) -> int:
    require_python_cache_isolation()
    output_dir = args.output_dir
    require_outside_checkout(output_dir)
    if output_dir.exists() or output_dir.is_symlink():
        raise ValueError(f"run-all output directory must be new: {output_dir}")

    reuse_from = getattr(args, "reuse_from", None)
    if isinstance(reuse_from, Path):
        require_disjoint_trees(output_dir, reuse_from)

    commit = args.commit or git_head()
    run_id = args.run_id or str(uuid.uuid4())
    runner_os = args.runner_os or platform.system()
    runner_arch = args.runner_arch or platform.machine()
    identity = compute_kernel_identity()
    validate_source_identity(identity, commit)
    stage_identities = compute_stage_identities()
    context = collect_stage_context(runner_os=runner_os, runner_arch=runner_arch)
    candidates = (
        load_reuse_candidates(reuse_from, stage_identities=stage_identities, context=context)
        if isinstance(reuse_from, Path) else {}
    )
    output_dir.mkdir(parents=True)
    dispositions: dict[str, str] = {}
    previous: Path | None = None
    for stage in STAGE_PLAN:
        stage_dir = output_dir / f"{stage.index}-{stage.name}"
        candidate = candidates.get(stage.name)
        if candidate is not None:
            _copy_reuse_pair(
                candidate[1].parent, stage_dir,
                expected_receipt_digest=candidate[0]["receipt_digest"],
            )
            dispositions[stage.name] = "reused"
            print(
                f"kernel stage {stage.index} {stage.name}: reused "
                f"{candidate[0]['receipt_digest']} from commit "
                f"{candidate[0]['run']['source_commit']}",
                flush=True,
            )
            previous = stage_dir / RECEIPT_NAME
            selection = make_stage_selection(
                stage=stage, disposition="reused", receipt=read_json(previous),
                assembly_run={
                    "repository": args.repository, "workflow": args.workflow,
                    "run_id": run_id, "run_attempt": args.run_attempt,
                    "source_commit": commit,
                },
                current_identity=identity,
            )
            write_json_new(stage_dir / SELECTION_NAME, selection)
            continue
        stage_dir.mkdir()
        project_cache = ROOT / ".lake/build"
        exit_code = run_fixed_stage(
            repository=args.repository,
            workflow=args.workflow,
            run_id=run_id,
            run_attempt=args.run_attempt,
            commit=commit,
            name=stage.name,
            index=stage.index,
            script=stage.script,
            timeout_minutes=stage.timeout_minutes,
            log_path=stage_dir / LOG_NAME,
            output=stage_dir / RECEIPT_NAME,
            runner_os=runner_os,
            runner_arch=runner_arch,
            cache_policy="local-project-cache",
            cache_requested_key="local:.lake/build",
            cache_restored_key="local:.lake/build" if project_cache.exists() else "",
            previous_receipt_path=previous,
            expected_stage_identity=stage_identities[stage.name],
        )
        dispositions[stage.name] = "executed"
        print(f"kernel stage {stage.index} {stage.name}: executed", flush=True)
        previous = stage_dir / RECEIPT_NAME
        selection = make_stage_selection(
            stage=stage, disposition="executed", receipt=read_json(previous),
            assembly_run={
                "repository": args.repository, "workflow": args.workflow,
                "run_id": run_id, "run_attempt": args.run_attempt,
                "source_commit": commit,
            },
            current_identity=identity,
        )
        write_json_new(stage_dir / SELECTION_NAME, selection)
        if exit_code != 0:
            return exit_code

    final_identity = compute_kernel_identity()
    if final_identity != identity:
        raise ValueError("source identity changed during kernel run-all")
    final_stage_identities = compute_stage_identities()
    if final_stage_identities != stage_identities:
        raise ValueError("stage inputs changed during kernel run-all")
    final_context = collect_stage_context(runner_os=runner_os, runner_arch=runner_arch)
    if final_context != context:
        raise ValueError("execution context changed during kernel run-all")
    receipts = [
        (read_json(output_dir / f"{stage.index}-{stage.name}" / RECEIPT_NAME),
         output_dir / f"{stage.index}-{stage.name}" / LOG_NAME)
        for stage in STAGE_PLAN
    ]
    record = verify_run(
        receipts=receipts,
        current_identity=identity,
        repository=args.repository,
        workflow=args.workflow,
        run_id=run_id,
        run_attempt=args.run_attempt,
        commit=commit,
        current_stage_identities=stage_identities,
        current_context=context,
        dispositions=dispositions,
    )
    write_json_new(output_dir / SOURCE_IDENTITY_NAME, identity)
    write_json_new(output_dir / EXECUTION_RECORD_NAME, record)
    return 0


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    run = subparsers.add_parser("run-stage")
    run.add_argument("--previous-receipt", type=Path)
    run.add_argument("--repository", required=True)
    run.add_argument("--workflow", required=True)
    run.add_argument("--run-id", required=True)
    run.add_argument("--run-attempt", required=True)
    run.add_argument("--commit", required=True)
    run.add_argument("--family", required=True)
    run.add_argument("--stage-index", type=int, required=True)
    run.add_argument("--script", required=True)
    run.add_argument("--timeout-minutes", type=int, required=True)
    run.add_argument("--log", type=Path, required=True)
    run.add_argument("--runner-os", required=True)
    run.add_argument("--runner-arch", required=True)
    run.add_argument("--cache-policy", required=True)
    run.add_argument("--cache-requested-key", required=True)
    run.add_argument("--cache-restored-key", default="")
    run.add_argument("--output", type=Path, required=True)
    run.set_defaults(handler=run_stage_cli)

    verify = subparsers.add_parser("verify-run")
    verify.add_argument("--identity", type=Path, required=True)
    verify.add_argument("--receipts-dir", type=Path, required=True)
    verify.add_argument("--repository", required=True)
    verify.add_argument("--workflow", required=True)
    verify.add_argument("--run-id", required=True)
    verify.add_argument("--run-attempt", required=True)
    verify.add_argument("--commit", required=True)
    verify.add_argument("--output", type=Path, required=True)
    verify.set_defaults(handler=verify_run_cli)

    run_all = subparsers.add_parser("run-all")
    run_all.add_argument("--output-dir", type=Path, required=True)
    run_all.add_argument("--repository", default="local/CertifiedJL")
    run_all.add_argument("--workflow", default="Local kernel proof record")
    run_all.add_argument("--run-id")
    run_all.add_argument("--run-attempt", default="1")
    run_all.add_argument("--commit")
    run_all.add_argument("--runner-os")
    run_all.add_argument("--runner-arch")
    run_all.add_argument(
        "--reuse-from", type=Path,
        help="canonical prior run-all directory (complete or failed prefix)",
    )
    run_all.set_defaults(handler=run_all_cli)

    args = parser.parse_args()
    try:
        result = args.handler(args)
    except (NativeReplayError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    raise SystemExit(0 if result is None else result)


if __name__ == "__main__":
    main()
