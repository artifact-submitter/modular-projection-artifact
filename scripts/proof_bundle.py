#!/usr/bin/env python3
"""Build and verify portable CertifiedJL proof and submission bundles.

The proof archive is deliberately independent of a Git checkout.  Every regular
file is named and hashed in its manifest; archive verification rejects links,
special files, duplicate paths, missing files, and unlisted files before an
optional clean extraction.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import importlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from typing import Any, Iterable, Mapping, Sequence


SCHEMA_VERSION = 1
MANIFEST_NAME = "proof-bundle-manifest.json"
RECEIPT_NAME = "validation-receipt.json"
REVIEW_NAME = "Review.lean"
THEOREM_MAP_NAME = "theorem-map.json"
REVIEW_WORKSPACE_NAME = "review.code-workspace"
PACKAGE_OVERRIDES_NAME = "source/.lake/release-package-overrides.json"
LAKE_WRAPPER_NAME = "review-bin/lake"
SUBMISSION_MANIFEST_NAME = "submission-manifest.json"
PROOF_ARCHIVE_NAME = "proof/proof-bundle.tar"
ALIGNMENT_REVIEW_NAME = "alignment-review.json"
FREEZE_POINTER_KIND = "certifiedjl-proof-freeze-pointer"
ANONYMOUS_SOURCE_MARKER = "anonymous-source.json"
SHA256_PREFIX = "sha256:"
SOURCE_EXCLUDES = {".git", "paper", "docs", "__pycache__"}
TREE_EXCLUDES = {".git", "__pycache__"}

LAKE_WRAPPER = b"""#!/bin/sh
set -eu
bundle_root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd -P)
exec "$bundle_root/toolchain/bin/lake" \\
  --packages="$bundle_root/source/.lake/release-package-overrides.json" "$@"
"""

ANONYMOUS_SOURCE_PROFILE = {
    "schema_version": 1,
    "record_kind": "anonymous-source",
    "policy": "first-party-author-metadata",
    "third_party_attributions": "preserved",
}


def _review_guidance(anonymous_source: bool) -> dict[str, object]:
    return {
        "guidance_kind": "non-attesting-review-guidance",
        "review_role": (
            "independent-anonymous-artifact-reviewer"
            if anonymous_source else "independent-artifact-reviewer"
        ),
        "records_human_approval": False,
    }


class BundleError(ValueError):
    """Raised when a bundle cannot be trusted or created safely."""


def canonical_digest(domain: str, value: object) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    return SHA256_PREFIX + hashlib.sha256(domain.encode() + b"\0" + encoded).hexdigest()


def sha256_bytes(data: bytes) -> str:
    return SHA256_PREFIX + hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return SHA256_PREFIX + digest.hexdigest()


def _canonical_mode(mode: int) -> int:
    return 0o755 if mode & 0o111 else 0o644


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n").encode()


def _regular_file(path: Path, label: str) -> None:
    try:
        info = path.lstat()
    except FileNotFoundError as exc:
        raise BundleError(f"missing {label}: {path}") from exc
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        raise BundleError(f"{label} must be a regular file: {path}")


def _is_anonymous_source(root: Path) -> bool:
    marker = root / ANONYMOUS_SOURCE_MARKER
    if not marker.exists() and not marker.is_symlink():
        return False
    _regular_file(marker, "anonymous source marker")
    try:
        profile = json.loads(marker.read_text(encoding="utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BundleError("anonymous source marker is invalid JSON") from exc
    if profile != ANONYMOUS_SOURCE_PROFILE:
        raise BundleError("anonymous source marker has an unexpected profile")
    return True


@contextmanager
def _identity_source(root: Path, *, anonymous_source: bool):
    """Yield the identity root for an identified or anonymous frozen profile."""
    root = root.resolve(strict=True)
    marked = _is_anonymous_source(root)
    if marked:
        if not anonymous_source:
            raise BundleError("anonymous source cannot represent an identified proof profile")
        yield root
        return
    if not anonymous_source:
        yield root
        return
    # This private preparation helper is deliberately absent from public
    # anonymous exports. It is needed only to compare an identified checkout
    # with a frozen anonymous identity.
    try:
        module = importlib.import_module("anonymous_export")
        projected_source = getattr(module, "projected_source")
    except (ImportError, ModuleNotFoundError, AttributeError) as exc:
        raise BundleError(
            "private anonymous projection helper is required for an identified checkout"
        ) from exc
    with projected_source(root) as projected:
        projected = Path(projected).resolve(strict=True)
        if not _is_anonymous_source(projected):
            raise BundleError("anonymous projection helper returned an unmarked source tree")
        yield projected


def _safe_relative(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    if (not value or value != path.as_posix() or path.is_absolute()
            or any(part in {"", ".", ".."} for part in path.parts)):
        raise BundleError(f"unsafe archive path: {value!r}")
    return path


def _iter_tree(root: Path, *, exclude: set[str]) -> Iterable[Path]:
    """Yield a stable regular-file tree and reject every in-tree link/special."""
    if root.is_symlink():
        # A dependency cache commonly exposes its package root as a symlink.
        root = root.resolve(strict=True)
    if not root.is_dir():
        raise BundleError(f"tree root is not a directory: {root}")
    for current, directories, files in os.walk(root, followlinks=False):
        current_path = Path(current)
        kept: list[str] = []
        for name in sorted(directories):
            if name in exclude:
                continue
            child = current_path / name
            if child.is_symlink():
                raise BundleError(f"nested directory symlink is not portable: {child}")
            if not child.is_dir():
                raise BundleError(f"non-directory encountered while scanning: {child}")
            kept.append(name)
        directories[:] = kept
        for name in sorted(files):
            if name in exclude or name.endswith(".pyc"):
                continue
            child = current_path / name
            _regular_file(child, "tree member")
            yield child


def _copy_file(source: Path, destination: Path) -> None:
    _regular_file(source, "source file")
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists() or destination.is_symlink():
        raise BundleError(f"duplicate bundle destination: {destination}")
    with source.open("rb") as input_stream, destination.open("xb") as output_stream:
        shutil.copyfileobj(input_stream, output_stream, 1024 * 1024)
    os.chmod(destination, _canonical_mode(source.stat().st_mode))


def _copy_tree(source: Path, destination: Path, *, exclude: set[str]) -> None:
    resolved = source.resolve(strict=True) if source.is_symlink() else source
    for path in _iter_tree(source, exclude=exclude):
        _copy_file(path, destination / path.relative_to(resolved))


def _copy_release_build_tree(source: Path, destination: Path, release: Any) -> None:
    resolved_root = source.resolve(strict=True)
    if not resolved_root.is_dir():
        raise BundleError(f"build tree root is not a directory: {source}")
    for current, directories, files in os.walk(resolved_root, followlinks=False):
        current_path = Path(current)
        kept = []
        for name in sorted(directories):
            child = current_path / name
            if name in TREE_EXCLUDES:
                continue
            if child.is_symlink():
                raise BundleError(f"build directory symlink is not portable: {child}")
            if not child.is_dir():
                raise BundleError(f"non-directory encountered in build tree: {child}")
            kept.append(name)
        directories[:] = kept
        for name in sorted(files):
            path = current_path / name
            relative = path.relative_to(resolved_root)
            if not release.is_release_build_artifact(relative):
                continue
            copy_source = path
            if path.is_symlink():
                try:
                    copy_source = path.resolve(strict=True)
                    copy_source.relative_to(resolved_root)
                except (OSError, ValueError) as exc:
                    raise BundleError(
                        f"build artifact symlink is broken or escapes its tree: {path}"
                    ) from exc
            _copy_file(copy_source, destination / relative)


def _copy_dependency_tree(source: Path, destination: Path, release: Any) -> None:
    """Copy pinned tracked sources plus the reusable package build projection."""
    resolved = source.resolve(strict=True)
    try:
        tracked = subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=resolved, stderr=subprocess.STDOUT,
        )
    except subprocess.CalledProcessError as exc:
        raise BundleError(f"cannot enumerate pinned dependency sources: {source}") from exc
    for raw in tracked.split(b"\0"):
        if not raw:
            continue
        relative = Path(os.fsdecode(raw))
        if relative.parts[:2] == (".lake", "build"):
            continue
        candidate = resolved / relative
        copy_source = candidate.resolve(strict=True) if candidate.is_symlink() else candidate
        if candidate.is_symlink():
            try:
                copy_source.relative_to(resolved)
            except ValueError as exc:
                raise BundleError(
                    f"tracked dependency symlink escapes package root: {relative}"
                ) from exc
        _copy_file(copy_source, destination / relative)
    build = resolved / ".lake" / "build"
    _copy_release_build_tree(build, destination / ".lake" / "build", release)


def _copy_materialized_tree(source: Path, destination: Path) -> None:
    """Copy a tree while materializing links and rejecting cycles/special files."""
    def visit(directory: Path, relative: Path, ancestors: frozenset[tuple[int, int]]) -> None:
        resolved_directory = directory.resolve(strict=True)
        identity = (resolved_directory.stat().st_dev, resolved_directory.stat().st_ino)
        if identity in ancestors:
            raise BundleError(f"linked tree contains a cycle: {directory}")
        next_ancestors = ancestors | {identity}
        for child in sorted(directory.iterdir(), key=lambda path: path.name):
            child_relative = relative / child.name
            resolved = child.resolve(strict=True)
            if resolved.is_dir():
                visit(child, child_relative, next_ancestors)
            elif resolved.is_file():
                _copy_file(resolved, destination / child_relative)
            else:
                raise BundleError(f"linked tree contains a special file: {child}")

    visit(source, Path(), frozenset())


def _git_tracked_files(root: Path) -> list[Path]:
    try:
        output = subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=root, stderr=subprocess.STDOUT,
        )
    except subprocess.CalledProcessError as exc:
        raise BundleError("proof-bundle build requires a Git source checkout") from exc
    result: list[Path] = []
    for raw in output.split(b"\0"):
        if not raw:
            continue
        relative = Path(os.fsdecode(raw))
        if relative.parts and relative.parts[0] in SOURCE_EXCLUDES:
            continue
        path = root / relative
        _regular_file(path, "tracked source")
        result.append(relative)
    if not result:
        raise BundleError("source checkout has no tracked proof inputs")
    return sorted(result, key=lambda item: item.as_posix())


def _load_release_validation() -> Any:
    try:
        module = importlib.import_module("release_validation")
    except (ImportError, ModuleNotFoundError) as exc:
        raise BundleError("scripts/release_validation.py is required (fail closed)") from exc
    required = (
        "compute_release_identity", "compute_artifact_identity", "proof_identity_projection",
        "verify_release_receipt", "receipt_semantics", "write_frozen_source_manifest",
        "compute_validator_tool_identity", "verify_validator_tool_identity",
        "compute_toolchain_runtime_identity", "validator_tool_portable_projection",
        "validation_evidence_inventory", "write_frozen_package_source_manifest",
        "is_release_build_artifact",
    )
    missing = [name for name in required if not callable(getattr(module, name, None))]
    if missing:
        raise BundleError("release_validation API is incomplete: " + ", ".join(missing))
    return module


def _release_semantics(project_root: Path, receipt_path: Path) -> tuple[dict, dict, dict, str]:
    validation = _load_release_validation()
    identity = validation.compute_release_identity(project_root)
    if not isinstance(identity, dict):
        raise BundleError("release identity API returned a non-object")
    receipt = validation.verify_release_receipt(
        receipt_path, expected_proof_identity=identity, check_live_tools=False,
    )
    semantics = validation.receipt_semantics(receipt)
    if not isinstance(semantics, tuple) or len(semantics) not in {2, 3}:
        raise BundleError("release receipt semantics API returned an invalid result")
    if len(semantics) == 3:
        source_identity, artifact_identity, receipt_digest = semantics
    else:  # Temporary compatibility with pre-artifact API; packaging still fails below.
        source_identity, receipt_digest = semantics
        artifact_identity = receipt.get("artifact_identity")
    if source_identity != identity:
        raise BundleError("release receipt does not bind the exact current inputs")
    if not isinstance(receipt_digest, str) or not receipt_digest.startswith(SHA256_PREFIX):
        raise BundleError("release receipt has no canonical semantic digest")
    proof_identity = validation.proof_identity_projection(identity)
    if not isinstance(proof_identity, dict):
        raise BundleError("release proof projection API returned a non-object")
    if not isinstance(artifact_identity, dict):
        raise BundleError("release receipt does not bind a compiled artifact identity")
    return receipt, proof_identity, artifact_identity, receipt_digest


def _inventory(root: Path, roles: Mapping[str, str]) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    for path in _iter_tree(root, exclude=set()):
        relative = path.relative_to(root).as_posix()
        role = next((value for prefix, value in roles.items()
                     if relative == prefix or relative.startswith(prefix + "/")), "other")
        records.append({
            "path": relative,
            "sha256": sha256_file(path),
            "size": path.stat().st_size,
            "mode": _canonical_mode(path.stat().st_mode),
            "role": role,
        })
    records.sort(key=lambda value: str(value["path"]))
    return records


def _manifest_digest(manifest: Mapping[str, object], *, submission: bool = False) -> str:
    field = "submission_id" if submission else "bundle_id"
    unsigned = {key: value for key, value in manifest.items() if key != field}
    domain = "CertifiedJL-submission-bundle-v1" if submission else "CertifiedJL-proof-bundle-v1"
    return canonical_digest(domain, unsigned)


def _write_deterministic_tar(source_root: Path, output: Path, manifest_name: str) -> None:
    if output.exists() or output.is_symlink():
        raise BundleError(f"output archive must be new: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    files = list(_iter_tree(source_root, exclude=set()))
    files.sort(key=lambda path: (path.name != manifest_name, path.relative_to(source_root).as_posix()))
    try:
        with output.open("xb") as raw, tarfile.open(fileobj=raw, mode="w", format=tarfile.PAX_FORMAT) as archive:
            for path in files:
                relative = path.relative_to(source_root).as_posix()
                info = tarfile.TarInfo(relative)
                info.size = path.stat().st_size
                info.mode = _canonical_mode(path.stat().st_mode)
                info.mtime = 0
                info.uid = info.gid = 0
                info.uname = info.gname = ""
                with path.open("rb") as stream:
                    archive.addfile(info, stream)
    except Exception:
        output.unlink(missing_ok=True)
        raise


def _dependency_entries(
    project_root: Path, packages_root: Path,
) -> tuple[list[tuple[str, Path, str]], dict[str, object]]:
    manifest_path = project_root / "lake-manifest.json"
    _regular_file(manifest_path, "Lake manifest")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise BundleError("Lake manifest has no dependency package list")
    result: list[tuple[str, Path, str]] = []
    overrides: list[dict[str, object]] = []
    names: set[str] = set()
    for package in packages:
        if not isinstance(package, dict):
            raise BundleError("invalid Lake package record")
        name, revision = package.get("name"), package.get("rev")
        if (not isinstance(name, str) or not name or "/" in name or name in names
                or not isinstance(revision, str) or not revision
                or package.get("type") != "git"):
            raise BundleError("Lake dependency name/revision is invalid or duplicated")
        names.add(name)
        path = packages_root / name
        resolved = path.resolve(strict=True)
        if not resolved.is_dir():
            raise BundleError(f"dependency source is not a directory: {path}")
        try:
            actual = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=resolved, text=True,
                stderr=subprocess.STDOUT,
            ).strip()
        except subprocess.CalledProcessError as exc:
            raise BundleError(f"dependency is not a revision-verifiable checkout: {name}") from exc
        if actual != revision:
            raise BundleError(f"dependency revision mismatch for {name}: {actual} != {revision}")
        status_output = subprocess.check_output(
            ["git", "status", "--porcelain", "--untracked-files=no"],
            cwd=resolved, text=True, stderr=subprocess.STDOUT,
        ).strip()
        if status_output:
            raise BundleError(f"dependency checkout is dirty: {name}")
        result.append((name, path, revision))
        sub_dir = package.get("subDir")
        if sub_dir is not None and not isinstance(sub_dir, str):
            raise BundleError(f"Lake dependency subdirectory is invalid: {name}")
        logical_dir = PurePosixPath(".lake", "packages", name)
        if sub_dir:
            logical_dir /= _safe_relative(sub_dir)
        config_file = package.get("configFile", "lakefile.lean")
        manifest_file = package.get("manifestFile", "lake-manifest.json")
        scope = package.get("scope", "")
        inherited = package.get("inherited", False)
        if (not isinstance(config_file, str) or not isinstance(manifest_file, str)
                or not isinstance(scope, str) or not isinstance(inherited, bool)):
            raise BundleError(f"Lake dependency metadata is invalid: {name}")
        _safe_relative(config_file)
        _safe_relative(manifest_file)
        overrides.append({
            "type": "path", "scope": scope, "name": name,
            "manifestFile": manifest_file, "inherited": inherited,
            "dir": logical_dir.as_posix(), "configFile": config_file,
        })
    version = manifest.get("version")
    if not isinstance(version, str) or not version:
        raise BundleError("Lake manifest version is invalid")
    return result, {"schemaVersion": version, "packages": overrides}


def _find_bound_file(value: object, filename: str, digest: str, size: int) -> bool:
    if isinstance(value, dict):
        label = value.get("path", value.get("name"))
        found_digest = value.get("sha256", value.get("digest"))
        found_size = value.get("size", value.get("size_bytes"))
        if (isinstance(label, str) and PurePosixPath(label).name == filename
                and found_digest == digest and (found_size is None or found_size == size)):
            return True
        return any(_find_bound_file(item, filename, digest, size) for item in value.values())
    if isinstance(value, list):
        return any(_find_bound_file(item, filename, digest, size) for item in value)
    return False


def _receipt_evidence_records(receipt: Mapping[str, object]) -> list[dict[str, object]]:
    """Select external receipt evidence that is not represented by artifact identity."""
    by_path: dict[str, dict[str, object]] = {}
    for value in _load_release_validation().validation_evidence_inventory(receipt):
        role = "receipt-bound-evidence"
        if not isinstance(value, dict):
            raise BundleError(f"release receipt evidence record is missing: {role}")
        path, size, digest = value.get("path"), value.get("size_bytes"), value.get("sha256")
        if (not isinstance(path, str) or not isinstance(size, int) or size < 0
                or not isinstance(digest, str)):
            raise BundleError(f"release receipt evidence record is invalid: {role}")
        path = _safe_relative(path).as_posix()
        record = {
            "receipt_path": path,
            "bundle_path": f"validation-evidence/{path}",
            "size": size,
            "sha256": digest,
            "role": role,
        }
        previous = by_path.get(path)
        if previous is not None and (previous["size"], previous["sha256"]) != (size, digest):
            raise BundleError(f"release receipt gives conflicting evidence identities: {path}")
        by_path[path] = record
    return [by_path[path] for path in sorted(by_path)]


def build_proof_bundle(
    *, project_root: Path, project_build: Path, packages_root: Path,
    receipt_path: Path, output: Path,
) -> dict[str, object]:
    project_root = project_root.resolve(strict=True)
    anonymous_source = _is_anonymous_source(project_root)
    _regular_file(receipt_path, "release validation receipt")
    receipt, proof_identity, artifact_identity, receipt_digest = _release_semantics(
        project_root, receipt_path,
    )
    dependencies, package_overrides = _dependency_entries(project_root, packages_root)
    evidence_records = _receipt_evidence_records(receipt)
    with tempfile.TemporaryDirectory(prefix="certifiedjl-proof-bundle-") as directory:
        staging = Path(directory)
        source = staging / "source"
        tracked_relatives = _git_tracked_files(project_root)
        for relative in tracked_relatives:
            _copy_file(project_root / relative, source / relative)

        release = _load_release_validation()
        release.write_frozen_source_manifest(
            source, (source / relative for relative in tracked_relatives),
            source / "release-source-manifest.json",
        )

        # Recompute from the copied, checkout-free tree: this is the portability
        # check and catches an omitted or extra proof/procedure input.
        copied_identity = release.compute_release_identity(source)
        if copied_identity != receipt["source_identity"]:
            raise BundleError("copied source tree does not reproduce the validated identity")

        _copy_release_build_tree(project_build, source / ".lake" / "build", release)
        if not any((source / ".lake" / "build").rglob("*.olean")):
            raise BundleError("project build tree contains no .olean artifacts")
        dependency_manifest: list[dict[str, object]] = []
        (source / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
        for name, path, revision in dependencies:
            destination = source / ".lake" / "packages" / name
            _copy_dependency_tree(path, destination, release)
            release.write_frozen_package_source_manifest(
                path.resolve(strict=True),
                destination / ".lake" / "release-package-source-manifest.json",
            )
            if not any((destination / ".lake" / "build").rglob("*.olean")):
                raise BundleError(f"dependency {name} has no compiled .olean artifacts")
            dependency_manifest.append({"name": name, "revision": revision})

        override_path = staging.joinpath(*PurePosixPath(PACKAGE_OVERRIDES_NAME).parts)
        override_path.write_bytes(_json_bytes(package_overrides))
        wrapper_path = staging.joinpath(*PurePosixPath(LAKE_WRAPPER_NAME).parts)
        wrapper_path.parent.mkdir(parents=True, exist_ok=True)
        wrapper_path.write_bytes(LAKE_WRAPPER)
        wrapper_path.chmod(0o755)

        copied_artifact_identity = _load_release_validation().compute_artifact_identity(
            source / ".lake" / "build", source / ".lake" / "packages",
        )
        if copied_artifact_identity != artifact_identity:
            raise BundleError("copied build/dependency tree differs from validated artifacts")

        generator = source / "scripts" / "reviewer_workspace.py"
        _regular_file(generator, "reviewer workspace generator")
        generated = staging / ".generated-review"
        subprocess.run(
            [sys.executable, str(generator), "--root", str(source), "--output", str(generated)],
            check=True,
        )
        for name in (REVIEW_NAME, THEOREM_MAP_NAME):
            generated_file = generated / name
            _regular_file(generated_file, f"generated {name}")
            digest, size = sha256_file(generated_file), generated_file.stat().st_size
            if not _find_bound_file(receipt, name, digest, size):
                raise BundleError(f"release receipt does not bind generated {name}")
            _copy_file(generated_file, staging / name)
        shutil.rmtree(generated)

        reviewer_directory = source / ".lake" / "release-reviewer-workspace"
        reviewer_records = receipt["reviewer_workspace"]
        for field, name in (("review_lean", REVIEW_NAME),
                            ("theorem_map", THEOREM_MAP_NAME),
                            ("review_olean", "Review.olean")):
            record = reviewer_records[field]
            evidence_source = receipt_path.parent.joinpath(
                *PurePosixPath(str(record["path"])).parts
            )
            _copy_file(evidence_source, reviewer_directory / name)
        workspace_document = {
            "folders": [{"path": "source"}],
            "settings": {
                "lean4.envPathExtensions": ["../review-bin", "../toolchain/bin"],
                "lean4.automaticallyBuildDependencies": False,
                "lean4.alwaysAskBeforeInstallingLeanVersions": True,
            },
        }
        (staging / REVIEW_WORKSPACE_NAME).write_bytes(_json_bytes(workspace_document))

        _copy_file(receipt_path, staging / RECEIPT_NAME)
        for record in evidence_records:
            evidence_source = receipt_path.parent.joinpath(
                *PurePosixPath(str(record["receipt_path"])).parts
            )
            _regular_file(evidence_source, f"release evidence {record['receipt_path']}")
            if (evidence_source.stat().st_size != record["size"]
                    or sha256_file(evidence_source) != record["sha256"]):
                raise BundleError(
                    f"release evidence differs from receipt: {record['receipt_path']}"
                )
            _copy_file(
                evidence_source,
                staging.joinpath(*PurePosixPath(str(record["bundle_path"])).parts),
            )
        platform_record = {
            "system": platform.system(), "machine": platform.machine(),
            "python": platform.python_version(),
        }
        environment = receipt.get("environment")
        if not isinstance(environment, dict) or not isinstance(environment.get("tools"), dict):
            raise BundleError("release receipt does not bind validator tools")
        toolchain_record = release.compute_validator_tool_identity(project_root)
        if toolchain_record != environment["tools"]:
            raise BundleError("current toolchain differs from release validation tools")
        release.verify_validator_tool_identity(environment["tools"], project_root)
        selected_toolchain_root = Path(str(toolchain_record["selected_toolchain_root"]))
        for directory_name in ("bin", "lib"):
            _copy_materialized_tree(
                selected_toolchain_root / directory_name,
                staging / "toolchain" / directory_name,
            )
        packaged_runtime = release.compute_toolchain_runtime_identity(staging / "toolchain")
        if (packaged_runtime.get("runtime_file_count") != toolchain_record.get("runtime_file_count")
                or packaged_runtime.get("runtime_digest") != toolchain_record.get("runtime_digest")):
            raise BundleError("copied toolchain runtime differs from release validation")
        portable_toolchain = release.validator_tool_portable_projection(toolchain_record)
        roles = {
            "source/.lake/build": "project-build",
            "source/.lake/packages": "dependency-source-and-build",
            "source": "validated-source",
            "toolchain": "validated-toolchain-runtime",
            RECEIPT_NAME: "validation-receipt",
            "validation-evidence": "validation-evidence",
            REVIEW_NAME: "reviewer-entrypoint",
            THEOREM_MAP_NAME: "theorem-mapping",
            REVIEW_WORKSPACE_NAME: "offline-editor-workspace",
            LAKE_WRAPPER_NAME: "offline-lake-wrapper",
            PACKAGE_OVERRIDES_NAME: "offline-package-overrides",
        }
        files = _inventory(staging, roles)
        manifest: dict[str, object] = {
            "schema_version": SCHEMA_VERSION,
            "record_kind": "certifiedjl-proof-bundle",
            "anonymous_source": anonymous_source,
            "review_guidance": _review_guidance(anonymous_source),
            "proof_identity": proof_identity,
            "validation_procedure_digest": receipt["source_identity"][
                "validation_procedure_digest"
            ],
            "artifact_identity": artifact_identity,
            "validation": {
                "receipt_path": RECEIPT_NAME,
                "receipt_sha256": sha256_file(staging / RECEIPT_NAME),
                "receipt_digest": receipt_digest,
                "evidence": evidence_records,
            },
            "reviewer_workspace": {
                "entrypoint": REVIEW_NAME,
                "entrypoint_sha256": sha256_file(staging / REVIEW_NAME),
                "theorem_map": THEOREM_MAP_NAME,
                "theorem_map_sha256": sha256_file(staging / THEOREM_MAP_NAME),
                "compiled_review": "source/.lake/release-reviewer-workspace/Review.olean",
                "compiled_review_sha256": sha256_file(reviewer_directory / "Review.olean"),
                "editor_workspace": REVIEW_WORKSPACE_NAME,
                "lake_wrapper": LAKE_WRAPPER_NAME,
                "package_overrides": PACKAGE_OVERRIDES_NAME,
            },
            "platform": platform_record,
            "toolchain": portable_toolchain,
            "dependencies": dependency_manifest,
            "files": files,
        }
        manifest["bundle_id"] = _manifest_digest(manifest)
        (staging / MANIFEST_NAME).write_bytes(_json_bytes(manifest))
        _write_deterministic_tar(staging, output, MANIFEST_NAME)
    try:
        verify_proof_bundle(output)
    except Exception:
        output.unlink(missing_ok=True)
        raise
    return manifest


def _verified_archive(
    path: Path, manifest_name: str, *, capture: set[str] | None = None,
) -> tuple[dict[str, object], dict[str, bytes], set[str]]:
    """Verify an archive by streaming file contents, retaining only small captures."""
    _regular_file(path, "archive")
    capture = set() if capture is None else capture
    captured: dict[str, bytes] = {}
    try:
        with tarfile.open(path, mode="r:*") as archive:
            members: dict[str, tarfile.TarInfo] = {}
            for member in archive.getmembers():
                name = _safe_relative(member.name).as_posix()
                if not member.isfile():
                    raise BundleError(
                        f"archive contains a link, directory, or special member: {name}"
                    )
                if name in members:
                    raise BundleError(f"archive contains duplicate member: {name}")
                members[name] = member
            manifest_member = members.get(manifest_name)
            if manifest_member is None:
                raise BundleError(f"archive is missing {manifest_name}")
            if manifest_member.size > 128 * 1024 * 1024:
                raise BundleError(f"unreasonably large {manifest_name}")
            stream = archive.extractfile(manifest_member)
            if stream is None:
                raise BundleError(f"cannot read {manifest_name}")
            manifest_bytes = stream.read()
            try:
                manifest = json.loads(manifest_bytes)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise BundleError(f"invalid {manifest_name}") from exc
            if not isinstance(manifest, dict):
                raise BundleError(f"{manifest_name} must contain a JSON object")
            captured[manifest_name] = manifest_bytes

            records = manifest.get("files")
            if not isinstance(records, list):
                raise BundleError("manifest file inventory is missing")
            expected = {manifest_name}
            record_by_path: dict[str, dict[str, object]] = {}
            for record in records:
                if (not isinstance(record, dict)
                        or set(record) != {"path", "sha256", "size", "mode", "role"}):
                    raise BundleError("invalid file inventory record")
                relative = record.get("path")
                if not isinstance(relative, str):
                    raise BundleError("invalid inventory path")
                relative = _safe_relative(relative).as_posix()
                if relative == manifest_name or relative in record_by_path:
                    raise BundleError(f"duplicate or recursive inventory path: {relative}")
                if (not isinstance(record.get("mode"), int)
                        or record["mode"] not in {0o644, 0o755}
                        or not isinstance(record.get("role"), str)):
                    raise BundleError(f"invalid inventory metadata: {relative}")
                record_by_path[relative] = record
                expected.add(relative)
            unexpected = sorted(set(members) - expected)
            missing = sorted(expected - set(members))
            if unexpected:
                raise BundleError("archive contains unlisted files: " + ", ".join(unexpected[:5]))
            if missing:
                raise BundleError("archive is missing inventoried files: " + ", ".join(missing[:5]))

            for name, record in record_by_path.items():
                member = members[name]
                if member.size != record.get("size") or (member.mode & 0o777) != record["mode"]:
                    raise BundleError(f"archive file size/mode mismatch: {name}")
                stream = archive.extractfile(member)
                if stream is None:
                    raise BundleError(f"cannot read archive member: {name}")
                digest = hashlib.sha256()
                retained = bytearray() if name in capture else None
                if retained is not None and member.size > 128 * 1024 * 1024:
                    raise BundleError(f"captured archive member is unreasonably large: {name}")
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
                    if retained is not None:
                        retained.extend(chunk)
                if SHA256_PREFIX + digest.hexdigest() != record.get("sha256"):
                    raise BundleError(f"archive file hash mismatch: {name}")
                if retained is not None:
                    captured[name] = bytes(retained)
    except tarfile.TarError as exc:
        raise BundleError(f"invalid tar archive: {path}") from exc
    return manifest, captured, set(members)


def _materialize_archive(
    archive_path: Path, destination: Path, *, prefix: str | None = None,
) -> None:
    """Materialize already-verified regular members without tarfile.extract."""
    with tarfile.open(archive_path, mode="r:*") as archive:
        for member in archive.getmembers():
            name = _safe_relative(member.name).as_posix()
            if prefix is not None and not name.startswith(prefix):
                continue
            target = destination.joinpath(*PurePosixPath(name).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            stream = archive.extractfile(member)
            if stream is None:
                raise BundleError(f"cannot materialize archive member: {name}")
            with target.open("xb") as output:
                shutil.copyfileobj(stream, output, 1024 * 1024)
            os.chmod(target, member.mode & 0o777)


def _copy_archive_member(archive_path: Path, name: str, output: Path) -> None:
    with tarfile.open(archive_path, mode="r:*") as archive:
        member = archive.getmember(name)
        stream = archive.extractfile(member)
        if stream is None:
            raise BundleError(f"cannot read archive member: {name}")
        with output.open("xb") as destination:
            shutil.copyfileobj(stream, destination, 1024 * 1024)


def _verify_embedded_receipt(
    archive_path: Path, files: Mapping[str, bytes], manifest: Mapping[str, object],
) -> None:
    validation = manifest.get("validation")
    if not isinstance(validation, dict) or validation.get("receipt_path") != RECEIPT_NAME:
        raise BundleError("proof manifest has invalid validation binding")
    receipt_data = files.get(RECEIPT_NAME)
    if receipt_data is None or validation.get("receipt_sha256") != sha256_bytes(receipt_data):
        raise BundleError("proof manifest receipt hash mismatch")
    with tempfile.TemporaryDirectory(prefix="certifiedjl-receipt-verify-") as directory:
        path = Path(directory) / RECEIPT_NAME
        path.write_bytes(receipt_data)
        evidence_records = validation.get("evidence")
        if not isinstance(evidence_records, list):
            raise BundleError("proof manifest has no validation evidence inventory")
        for record in evidence_records:
            if not isinstance(record, dict):
                raise BundleError("proof manifest has an invalid evidence record")
            receipt_relative = _safe_relative(str(record.get("receipt_path", "")))
            bundle_relative = _safe_relative(str(record.get("bundle_path", "")))
            destination = Path(directory).joinpath(*receipt_relative.parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            _copy_archive_member(archive_path, bundle_relative.as_posix(), destination)
        release = _load_release_validation()
        receipt = release.verify_release_receipt(
            path, expected_proof_identity=manifest.get("proof_identity"),
            evidence_root=Path(directory), check_live_tools=False,
        )
        semantics = release.receipt_semantics(receipt)
        if not isinstance(semantics, tuple) or len(semantics) not in {2, 3}:
            raise BundleError("invalid embedded receipt semantics")
        if len(semantics) == 3:
            _identity, receipt_artifacts, semantic_digest = semantics
        else:
            _identity, semantic_digest = semantics
            receipt_artifacts = receipt.get("artifact_identity")
    if semantic_digest != validation.get("receipt_digest"):
        raise BundleError("proof manifest receipt semantic digest mismatch")
    if receipt_artifacts != manifest.get("artifact_identity"):
        raise BundleError("proof manifest artifact identity differs from release receipt")
    if validation.get("evidence") != _receipt_evidence_records(receipt):
        raise BundleError("proof manifest does not bind complete release evidence")


def _verify_embedded_tree_identities(
    archive_path: Path, manifest: Mapping[str, object], *, check_host: bool = False,
) -> None:
    """Recompute proof and artifact identities from the packaged bytes."""
    with tempfile.TemporaryDirectory(prefix="certifiedjl-bundle-identity-") as directory:
        source = Path(directory) / "source"
        _materialize_archive(archive_path, Path(directory), prefix="source/")
        _materialize_archive(archive_path, Path(directory), prefix="toolchain/")
        (source / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
        release = _load_release_validation()
        if _is_anonymous_source(source) is not manifest.get("anonymous_source"):
            raise BundleError("embedded source anonymity profile differs from proof manifest")
        source_identity = release.compute_release_identity(source)
        if release.proof_identity_projection(source_identity) != manifest.get("proof_identity"):
            raise BundleError("embedded source tree does not reproduce frozen proof identity")
        artifact_identity = release.compute_artifact_identity(
            source / ".lake" / "build", source / ".lake" / "packages",
        )
        if artifact_identity != manifest.get("artifact_identity"):
            raise BundleError("embedded build/dependency files differ from validated artifacts")
        toolchain = manifest.get("toolchain")
        if not isinstance(toolchain, dict):
            raise BundleError("proof manifest has no portable toolchain identity")
        runtime = release.compute_toolchain_runtime_identity(Path(directory) / "toolchain")
        if (runtime.get("runtime_file_count") != toolchain.get("runtime_file_count")
                or runtime.get("runtime_digest") != toolchain.get("runtime_digest")):
            raise BundleError("embedded toolchain runtime differs from validated toolchain")
        executables = toolchain.get("executables")
        if not isinstance(executables, dict):
            raise BundleError("proof manifest has no portable validator executables")
        for name in ("lean", "lake", "leanchecker"):
            record = executables.get(name)
            if not isinstance(record, dict) or not isinstance(record.get("relative_path"), str):
                raise BundleError(f"proof manifest has no portable {name}")
            relative = _safe_relative(record["relative_path"])
            executable = Path(directory) / "toolchain"
            executable = executable.joinpath(*relative.parts)
            _regular_file(executable, f"bundled {name}")
            if sha256_file(executable) != record.get("sha256"):
                raise BundleError(f"bundled {name} differs from validator identity")
        if check_host:
            expected_platform = manifest.get("platform")
            if (not isinstance(expected_platform, dict)
                    or expected_platform.get("system") != platform.system()
                    or expected_platform.get("machine") != platform.machine()):
                raise BundleError("host platform differs from validated artifact platform")
            # The release validator records Lean's version for leanchecker;
            # leanchecker itself has no successful --version interface.
            for name in ("lean", "lake"):
                record = executables[name]
                executable = Path(directory) / "toolchain"
                executable = executable.joinpath(*PurePosixPath(record["relative_path"]).parts)
                version = subprocess.check_output(
                    [str(executable), "--version"], text=True, stderr=subprocess.STDOUT,
                ).strip()
                if version != record.get("version"):
                    raise BundleError(f"bundled {name} reports an unexpected version")


def verify_proof_bundle(
    path: Path, *, extract_to: Path | None = None, check_host: bool = False,
) -> dict[str, object]:
    manifest, captured, names = _verified_archive(
        path, MANIFEST_NAME, capture={
            RECEIPT_NAME, REVIEW_NAME, THEOREM_MAP_NAME, REVIEW_WORKSPACE_NAME,
            PACKAGE_OVERRIDES_NAME, LAKE_WRAPPER_NAME,
            "source/.lake/release-reviewer-workspace/Review.lean",
            "source/.lake/release-reviewer-workspace/theorem-map.json",
            "source/.lake/release-reviewer-workspace/Review.olean",
        },
    )
    if (manifest.get("schema_version") != SCHEMA_VERSION
            or manifest.get("record_kind") != "certifiedjl-proof-bundle"
            or not isinstance(manifest.get("anonymous_source"), bool)
            or manifest.get("review_guidance")
                != _review_guidance(bool(manifest.get("anonymous_source")))
            or manifest.get("bundle_id") != _manifest_digest(manifest)):
        raise BundleError("invalid proof bundle manifest or bundle ID")
    _verify_embedded_receipt(path, captured, manifest)
    _verify_embedded_tree_identities(path, manifest, check_host=check_host)
    reviewer = manifest.get("reviewer_workspace")
    if (not isinstance(reviewer, dict)
            or reviewer.get("entrypoint_sha256") != sha256_bytes(captured.get(REVIEW_NAME, b""))
            or reviewer.get("theorem_map_sha256") != sha256_bytes(captured.get(THEOREM_MAP_NAME, b""))
            or captured.get(REVIEW_NAME)
                != captured.get("source/.lake/release-reviewer-workspace/Review.lean")
            or captured.get(THEOREM_MAP_NAME)
                != captured.get("source/.lake/release-reviewer-workspace/theorem-map.json")
            or reviewer.get("compiled_review_sha256") != sha256_bytes(
                captured.get("source/.lake/release-reviewer-workspace/Review.olean", b"")
            )
            or reviewer.get("lake_wrapper") != LAKE_WRAPPER_NAME
            or reviewer.get("package_overrides") != PACKAGE_OVERRIDES_NAME
            or captured.get(LAKE_WRAPPER_NAME) != LAKE_WRAPPER):
        raise BundleError("reviewer workspace binding mismatch")
    try:
        editor_workspace = json.loads(captured[REVIEW_WORKSPACE_NAME])
    except (KeyError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BundleError("offline editor workspace is invalid") from exc
    if editor_workspace != {
        "folders": [{"path": "source"}],
        "settings": {
            "lean4.envPathExtensions": ["../review-bin", "../toolchain/bin"],
            "lean4.automaticallyBuildDependencies": False,
            "lean4.alwaysAskBeforeInstallingLeanVersions": True,
        },
    }:
        raise BundleError("offline editor workspace settings are unsafe or incomplete")
    if not any(name.endswith(".olean") and name.startswith("source/.lake/build/") for name in names):
        raise BundleError("proof bundle is missing project .olean artifacts")
    dependencies = manifest.get("dependencies")
    if not isinstance(dependencies, list):
        raise BundleError("proof bundle has no dependency records")
    try:
        package_overrides = json.loads(captured[PACKAGE_OVERRIDES_NAME])
    except (KeyError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BundleError("offline package overrides are invalid") from exc
    override_records = package_overrides.get("packages") if isinstance(package_overrides, dict) else None
    if (not isinstance(package_overrides, dict)
            or not isinstance(package_overrides.get("schemaVersion"), str)
            or not isinstance(override_records, list)
            or len(override_records) != len(dependencies)):
        raise BundleError("offline package overrides are incomplete")
    for dependency in dependencies:
        if not isinstance(dependency, dict) or not isinstance(dependency.get("name"), str):
            raise BundleError("invalid dependency record")
        prefix = f"source/.lake/packages/{dependency['name']}/.lake/build/"
        if not any(name.startswith(prefix) and name.endswith(".olean") for name in names):
            raise BundleError(f"proof bundle is missing dependency artifacts: {dependency['name']}")
    for dependency, override in zip(dependencies, override_records):
        name = dependency["name"]
        if (not isinstance(override, dict) or override.get("type") != "path"
                or override.get("name") != name or not isinstance(override.get("dir"), str)
                or not isinstance(override.get("configFile"), str)
                or not isinstance(override.get("manifestFile"), str)
                or not isinstance(override.get("scope"), str)
                or not isinstance(override.get("inherited"), bool)):
            raise BundleError(f"offline package override is invalid: {name}")
        directory = _safe_relative(override["dir"])
        expected_prefix = PurePosixPath(".lake", "packages", name)
        if directory != expected_prefix and expected_prefix not in directory.parents:
            raise BundleError(f"offline package override escapes dependency tree: {name}")
        _safe_relative(override["configFile"])
        _safe_relative(override["manifestFile"])
    if extract_to is not None:
        if extract_to.exists() or extract_to.is_symlink():
            raise BundleError(f"extraction destination must be new: {extract_to}")
        try:
            extract_to.mkdir(parents=True)
            _materialize_archive(path, extract_to)
            (extract_to / "source" / ".lake" / "packages").mkdir(
                parents=True, exist_ok=True,
            )
        except Exception:
            shutil.rmtree(extract_to, ignore_errors=True)
            raise
    return manifest


def _paper_inventory(paper_root: Path) -> list[dict[str, object]]:
    records = []
    for path in _iter_tree(paper_root, exclude=TREE_EXCLUDES):
        relative = path.relative_to(paper_root).as_posix()
        records.append({"path": relative, "sha256": sha256_file(path), "size": path.stat().st_size})
    if not records:
        raise BundleError("paper tree is empty")
    return sorted(records, key=lambda value: str(value["path"]))


def alignment_review_digest(review: Mapping[str, object]) -> str:
    return canonical_digest(
        "CertifiedJL-manuscript-proof-alignment-review-v1",
        {key: value for key, value in review.items() if key != "review_digest"},
    )


def _validate_alignment_review(
    review: object, *, paper_digest: str, proof_manifest: Mapping[str, object],
) -> dict[str, object]:
    if not isinstance(review, dict):
        raise BundleError("alignment review must be a JSON object")
    required = {
        "schema_version", "record_kind", "attests_human_review", "reviewer",
        "reviewed_utc", "paper_tree_digest", "proof_bundle_id",
        "theorem_map_sha256", "review_digest",
    }
    if set(review) != required:
        raise BundleError("alignment review has an unexpected schema")
    if (review.get("schema_version") != SCHEMA_VERSION
            or review.get("record_kind") != "certifiedjl-manuscript-proof-alignment-review"
            or review.get("attests_human_review") is not True
            or not isinstance(review.get("reviewer"), str) or not review["reviewer"].strip()
            or not isinstance(review.get("reviewed_utc"), str) or not review["reviewed_utc"].endswith("Z")
            or review.get("review_digest") != alignment_review_digest(review)):
        raise BundleError("alignment review is not a valid human-review record")
    if (review.get("paper_tree_digest") != paper_digest
            or review.get("proof_bundle_id") != proof_manifest.get("bundle_id")
            or review.get("theorem_map_sha256")
                != proof_manifest["reviewer_workspace"]["theorem_map_sha256"]):
        raise BundleError("alignment review does not bind this paper, proof, and theorem map")
    if (proof_manifest.get("anonymous_source") is True
            and review.get("reviewer")
                != proof_manifest["review_guidance"]["review_role"]):
        raise BundleError(
            "anonymous alignment review must use the fixed public reviewer role"
        )
    return review


def compose_submission(
    *, project_root: Path, paper_root: Path, proof_bundle: Path,
    alignment_review: Path, output: Path,
) -> dict[str, object]:
    proof_manifest = verify_proof_bundle(proof_bundle)
    release = _load_release_validation()
    anonymous_source = proof_manifest["anonymous_source"]
    with _identity_source(project_root, anonymous_source=anonymous_source) as identity_root:
        current_release = release.compute_release_identity(identity_root)
    current = release.proof_identity_projection(current_release)
    if current != proof_manifest.get("proof_identity"):
        raise BundleError("current proof inputs differ from the frozen validated bundle")
    if (current_release.get("validation_procedure_digest")
            != proof_manifest.get("validation_procedure_digest")):
        raise BundleError("validation procedure changed since the frozen proof was checked")
    paper_records = _paper_inventory(paper_root)
    paper_digest = canonical_digest("CertifiedJL-final-paper-tree-v1", paper_records)
    _regular_file(alignment_review, "manuscript/proof alignment review")
    review = _validate_alignment_review(
        json.loads(alignment_review.read_text(encoding="utf-8")),
        paper_digest=paper_digest, proof_manifest=proof_manifest,
    )
    with tempfile.TemporaryDirectory(prefix="certifiedjl-submission-") as directory:
        staging = Path(directory)
        _copy_file(proof_bundle, staging / PROOF_ARCHIVE_NAME)
        _copy_file(alignment_review, staging / ALIGNMENT_REVIEW_NAME)
        for record in paper_records:
            relative = Path(str(record["path"]))
            _copy_file(paper_root / relative, staging / "paper" / relative)
        submission: dict[str, object] = {
            "schema_version": SCHEMA_VERSION,
            "record_kind": "certifiedjl-submission-bundle",
            "proof_bundle": {
                "path": PROOF_ARCHIVE_NAME,
                "sha256": sha256_file(proof_bundle),
                "bundle_id": proof_manifest["bundle_id"],
                "anonymous_source": anonymous_source,
                "proof_identity": proof_manifest["proof_identity"],
                "theorem_map_sha256": proof_manifest["reviewer_workspace"]["theorem_map_sha256"],
            },
            "paper": {
                "root": "paper",
                "tree_digest": paper_digest,
                "files": paper_records,
            },
            "alignment_review": {
                "path": ALIGNMENT_REVIEW_NAME,
                "sha256": sha256_file(alignment_review),
                "review_digest": review["review_digest"],
            },
        }
        roles = {
            PROOF_ARCHIVE_NAME: "frozen-proof-bundle",
            ALIGNMENT_REVIEW_NAME: "manuscript-proof-alignment-review",
            "paper": "final-paper",
        }
        submission["files"] = _inventory(staging, roles)
        submission["submission_id"] = _manifest_digest(submission, submission=True)
        (staging / SUBMISSION_MANIFEST_NAME).write_bytes(_json_bytes(submission))
        _write_deterministic_tar(staging, output, SUBMISSION_MANIFEST_NAME)
    verify_submission(output)
    return submission


def verify_submission(path: Path, *, extract_to: Path | None = None) -> dict[str, object]:
    manifest, captured, names = _verified_archive(
        path, SUBMISSION_MANIFEST_NAME, capture={ALIGNMENT_REVIEW_NAME},
    )
    if (manifest.get("schema_version") != SCHEMA_VERSION
            or manifest.get("record_kind") != "certifiedjl-submission-bundle"
            or manifest.get("submission_id") != _manifest_digest(manifest, submission=True)):
        raise BundleError("invalid submission manifest or submission ID")
    proof = manifest.get("proof_bundle")
    if not isinstance(proof, dict) or proof.get("path") != PROOF_ARCHIVE_NAME:
        raise BundleError("submission has invalid proof-bundle binding")
    if PROOF_ARCHIVE_NAME not in names:
        raise BundleError("submission proof archive hash mismatch")
    with tempfile.TemporaryDirectory(prefix="certifiedjl-nested-proof-") as directory:
        nested = Path(directory) / "proof.tar"
        _copy_archive_member(path, PROOF_ARCHIVE_NAME, nested)
        if proof.get("sha256") != sha256_file(nested):
            raise BundleError("submission proof archive hash mismatch")
        proof_manifest = verify_proof_bundle(nested)
    if (proof.get("bundle_id") != proof_manifest.get("bundle_id")
            or proof.get("anonymous_source") is not proof_manifest.get("anonymous_source")
            or proof.get("proof_identity") != proof_manifest.get("proof_identity")
            or proof.get("theorem_map_sha256")
                != proof_manifest["reviewer_workspace"]["theorem_map_sha256"]):
        raise BundleError("submission does not bind the nested proof manifest")
    paper = manifest.get("paper")
    if not isinstance(paper, dict) or not isinstance(paper.get("files"), list):
        raise BundleError("submission paper binding is invalid")
    paper_records = paper["files"]
    if paper.get("tree_digest") != canonical_digest("CertifiedJL-final-paper-tree-v1", paper_records):
        raise BundleError("submission paper tree digest mismatch")
    expected_paper = {f"paper/{record['path']}" for record in paper_records if isinstance(record, dict)}
    actual_paper = {name for name in names if name.startswith("paper/")}
    if expected_paper != actual_paper:
        raise BundleError("submission paper file set mismatch")
    review_binding = manifest.get("alignment_review")
    review_data = captured.get(ALIGNMENT_REVIEW_NAME)
    if (not isinstance(review_binding, dict) or review_data is None
            or review_binding.get("path") != ALIGNMENT_REVIEW_NAME
            or review_binding.get("sha256") != sha256_bytes(review_data)):
        raise BundleError("submission alignment-review file binding is invalid")
    try:
        review = json.loads(review_data)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BundleError("submission alignment review is invalid JSON") from exc
    checked_review = _validate_alignment_review(
        review, paper_digest=paper["tree_digest"], proof_manifest=proof_manifest,
    )
    if review_binding.get("review_digest") != checked_review["review_digest"]:
        raise BundleError("submission alignment-review digest mismatch")
    if extract_to is not None:
        if extract_to.exists() or extract_to.is_symlink():
            raise BundleError(f"extraction destination must be new: {extract_to}")
        try:
            extract_to.mkdir(parents=True)
            _materialize_archive(path, extract_to)
        except Exception:
            shutil.rmtree(extract_to, ignore_errors=True)
            raise
    return manifest


def freeze_pointer_digest(pointer: Mapping[str, object]) -> str:
    return canonical_digest(
        "CertifiedJL-proof-freeze-pointer-v1",
        {key: value for key, value in pointer.items() if key != "pointer_digest"},
    )


def write_freeze_pointer(proof_bundle: Path, output: Path) -> dict[str, object]:
    """Write the small, commit-friendly identity needed by the CI freeze guard."""
    manifest = verify_proof_bundle(proof_bundle)
    _parsed, captured, _names = _verified_archive(proof_bundle, MANIFEST_NAME)
    pointer: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "record_kind": FREEZE_POINTER_KIND,
        "bundle_id": manifest["bundle_id"],
        "anonymous_source": manifest["anonymous_source"],
        "bundle_manifest_sha256": sha256_bytes(captured[MANIFEST_NAME]),
        "proof_identity": manifest["proof_identity"],
        "validation_procedure_digest": manifest["validation_procedure_digest"],
        "artifact_identity": manifest["artifact_identity"],
        "theorem_map_sha256": manifest["reviewer_workspace"]["theorem_map_sha256"],
    }
    pointer["pointer_digest"] = freeze_pointer_digest(pointer)
    if output.exists() or output.is_symlink():
        raise BundleError(f"freeze pointer output must be new: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(_json_bytes(pointer))
    return pointer


def check_freeze(project_root: Path, pointer_path: Path) -> dict[str, object]:
    """Cheaply guard frozen proof inputs without downloading the proof archive."""
    _regular_file(pointer_path, "proof freeze pointer")
    pointer = json.loads(pointer_path.read_text(encoding="utf-8"))
    if (not isinstance(pointer, dict)
            or pointer.get("schema_version") != SCHEMA_VERSION
            or pointer.get("record_kind") != FREEZE_POINTER_KIND
            or not isinstance(pointer.get("anonymous_source"), bool)
            or pointer.get("pointer_digest") != freeze_pointer_digest(pointer)):
        raise BundleError("invalid proof freeze pointer")
    release = _load_release_validation()
    with _identity_source(
        project_root, anonymous_source=pointer["anonymous_source"],
    ) as identity_root:
        current = release.compute_release_identity(identity_root)
    if release.proof_identity_projection(current) != pointer.get("proof_identity"):
        raise BundleError("live proof inputs differ from the committed freeze pointer")
    return pointer


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build", help="build a frozen portable proof archive")
    build.add_argument("--project-root", type=Path, default=Path.cwd())
    build.add_argument("--project-build", type=Path)
    build.add_argument("--packages-root", type=Path)
    build.add_argument("--validation-receipt", type=Path, required=True)
    build.add_argument("--output", type=Path, required=True)
    verify = subparsers.add_parser("verify", help="verify a proof archive without Git")
    verify.add_argument("archive", type=Path)
    verify.add_argument("--extract-to", type=Path)
    verify.add_argument("--check-host-toolchain", action="store_true")
    compose = subparsers.add_parser("compose", help="compose frozen proof and final paper")
    compose.add_argument("--project-root", type=Path, default=Path.cwd())
    compose.add_argument("--paper-root", type=Path, required=True)
    compose.add_argument("--proof-bundle", type=Path, required=True)
    compose.add_argument("--alignment-review", type=Path, required=True)
    compose.add_argument("--output", type=Path, required=True)
    verify_submission_parser = subparsers.add_parser(
        "verify-submission", help="verify a composed submission archive",
    )
    verify_submission_parser.add_argument("archive", type=Path)
    verify_submission_parser.add_argument("--extract-to", type=Path)
    pointer = subparsers.add_parser(
        "write-freeze-pointer", help="write a small CI guard from a proof archive",
    )
    pointer.add_argument("--proof-bundle", type=Path, required=True)
    pointer.add_argument("--output", type=Path, required=True)
    guard = subparsers.add_parser(
        "check-freeze", help="compare live proof inputs with a committed freeze pointer",
    )
    guard.add_argument("--project-root", type=Path, default=Path.cwd())
    guard.add_argument("--pointer", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "build":
            root = args.project_root.resolve()
            manifest = build_proof_bundle(
                project_root=root,
                project_build=args.project_build or root / ".lake" / "build",
                packages_root=args.packages_root or root / ".lake" / "packages",
                receipt_path=args.validation_receipt,
                output=args.output,
            )
            print(manifest["bundle_id"])
        elif args.command == "verify":
            manifest = verify_proof_bundle(
                args.archive, extract_to=args.extract_to,
                check_host=args.check_host_toolchain,
            )
            print(manifest["bundle_id"])
        elif args.command == "compose":
            manifest = compose_submission(
                project_root=args.project_root, paper_root=args.paper_root,
                proof_bundle=args.proof_bundle, alignment_review=args.alignment_review,
                output=args.output,
            )
            print(manifest["submission_id"])
        elif args.command == "verify-submission":
            print(verify_submission(args.archive, extract_to=args.extract_to)["submission_id"])
        elif args.command == "write-freeze-pointer":
            print(write_freeze_pointer(args.proof_bundle, args.output)["pointer_digest"])
        else:
            print(check_freeze(args.project_root, args.pointer)["pointer_digest"])
    except (BundleError, OSError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        print(f"proof_bundle: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
