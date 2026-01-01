#!/usr/bin/env python3
"""Rebuild every first-party Lean source from a verified frozen proof bundle.

This is an offline reviewer convenience workflow, not an authoritative release
validation receipt.  It starts with a new project build directory while reusing
the bundle's already-validated dependency artifacts and toolchain.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import sys
from typing import Mapping, Sequence

from release_validation import (
    GENERATED_MODULE,
    ReleaseValidationError,
    canonical_digest,
    compute_artifact_identity,
    compute_release_identity,
    compute_toolchain_runtime_identity,
    render_all_production,
    run_command,
    sha256_file,
    tracked_files,
    utc_now,
)


REPORT_NAME = "offline-rebuild-report.json"
FAILURE_NAME = "offline-rebuild-failure.json"


def _write_new(path: Path, value: Mapping[str, object]) -> None:
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def _module_records(identity: Mapping[str, object], category: str) -> list[str]:
    classification = identity["lean_source_classification"]
    records = classification["categories"][category]
    return [
        Path(record["path"]).with_suffix("").as_posix().replace("/", ".")
        for record in records
    ]


def _copy_frozen_sources(source: Path, workspace: Path) -> None:
    selected = tracked_files(source)
    for path in selected:
        relative = path.relative_to(source)
        destination = workspace / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
    shutil.copy2(source / "release-source-manifest.json",
                 workspace / "release-source-manifest.json")


def _expected_olean_paths(identity: Mapping[str, object]) -> set[Path]:
    categories = identity["lean_source_classification"]["categories"]
    return {
        Path(record["path"]).with_suffix(".olean")
        for records in categories.values()
        for record in records
    } | {Path(f"{GENERATED_MODULE}.olean")}


def _bound_bundle_hash(manifest: Mapping[str, object], relative: str) -> str:
    files = manifest.get("files")
    if not isinstance(files, list):
        raise ReleaseValidationError("verified bundle manifest has no file inventory")
    matches = [record for record in files if isinstance(record, dict)
               and record.get("path") == relative]
    if len(matches) != 1 or not isinstance(matches[0].get("sha256"), str):
        raise ReleaseValidationError(f"verified bundle does not bind file: {relative}")
    return str(matches[0]["sha256"])


def rebuild_verified_bundle(
    bundle_root: Path, workspace: Path, output_dir: Path,
    manifest: Mapping[str, object],
) -> dict[str, object]:
    """Run the offline rebuild after ``verify_proof_bundle`` has succeeded."""
    bundle_root = bundle_root.resolve(strict=True)
    if workspace.exists() or workspace.is_symlink():
        raise ReleaseValidationError(f"offline rebuild workspace must be new: {workspace}")
    if output_dir.exists() or output_dir.is_symlink():
        raise ReleaseValidationError(f"offline rebuild output must be new: {output_dir}")
    source = bundle_root / "source"
    receipt_path = bundle_root / "validation-receipt.json"
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    identity = receipt["source_identity"]
    output_dir.mkdir(parents=True)
    workspace.mkdir(parents=True)
    _copy_frozen_sources(source, workspace)
    if compute_release_identity(workspace) != identity:
        raise ReleaseValidationError("offline rebuild workspace differs from frozen source identity")
    packages = source / ".lake" / "packages"
    workspace_packages = workspace / ".lake" / "packages"
    workspace_packages.mkdir(parents=True)
    dependency_names = [record["name"] for record in identity["dependencies"]]
    for name in dependency_names:
        target = packages / name
        if not target.is_dir():
            raise ReleaseValidationError(f"frozen bundle dependency is missing: {name}")
        (workspace_packages / name).symlink_to(target.resolve(strict=True), target_is_directory=True)
    shutil.copy2(
        source / ".lake" / "release-package-overrides.json",
        workspace / ".lake" / "release-package-overrides.json",
    )
    workspace_override = workspace / ".lake" / "release-package-overrides.json"
    project_build = workspace / ".lake" / "build"
    if project_build.exists() or project_build.is_symlink():
        raise ReleaseValidationError("offline rebuild project build was not initially absent")

    lake = bundle_root / "review-bin" / "lake"
    lean = bundle_root / "toolchain" / "bin" / "lean"
    leanchecker = bundle_root / "toolchain" / "bin" / "leanchecker"
    for tool in (lake, lean, leanchecker):
        if tool.is_symlink() or not tool.is_file():
            raise ReleaseValidationError(f"frozen bundle tool is missing: {tool}")
    override_path = source / ".lake" / "release-package-overrides.json"
    wrapper_hash = sha256_file(lake)
    override_hash = sha256_file(override_path)
    if sha256_file(workspace_override) != override_hash:
        raise ReleaseValidationError("workspace package override copy is not exact")
    if wrapper_hash != _bound_bundle_hash(manifest, "review-bin/lake"):
        raise ReleaseValidationError("offline Lake wrapper differs from verified bundle")
    if override_hash != _bound_bundle_hash(
        manifest, "source/.lake/release-package-overrides.json"
    ):
        raise ReleaseValidationError("offline package override differs from verified bundle")
    expected_toolchain = manifest.get("toolchain")
    if not isinstance(expected_toolchain, dict):
        raise ReleaseValidationError("verified bundle has no toolchain identity")
    toolchain_before = compute_toolchain_runtime_identity(bundle_root / "toolchain")
    if (
        toolchain_before.get("runtime_file_count")
        != expected_toolchain.get("runtime_file_count")
        or toolchain_before.get("runtime_digest") != expected_toolchain.get("runtime_digest")
    ):
        raise ReleaseValidationError("offline toolchain differs from verified bundle")
    environment = os.environ.copy()
    environment.update({
        "LEAN_NUM_THREADS": "1", "LAKE_NO_CACHE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PATH": os.pathsep.join([
            str(bundle_root / "review-bin"), str(bundle_root / "toolchain" / "bin"),
            environment.get("PATH", ""),
        ]),
    })
    environment.pop("LAKE_ARTIFACT_CACHE", None)
    environment.pop("CERTIFIEDJL_NATIVE_BUILD_DIR", None)
    environment.pop("CERTIFIEDJL_NATIVE_SHADOW_DIR", None)
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    logs = output_dir / "logs"
    steps: list[dict[str, object]] = []
    started = utc_now()
    failure: ReleaseValidationError | None = None
    generated_artifacts: dict[str, object] = {}
    try:
        commands = (
            ("source-trust-scan", [sys.executable, "scripts/check_trust.py"]),
            ("preflight-all-library-module-targets", [
                sys.executable, "scripts/release_validation.py",
                "preflight-module-targets", "--root", ".",
            ]),
            ("explicit-all-production-module-build", [
                str(lake), "build", *identity["production_modules"],
            ]),
            ("explicit-all-certifiedjl-fast-module-build", [
                str(lake), "build", *_module_records(identity, "certifiedjl_fast"),
            ]),
            ("explicit-all-tests-module-build", [
                str(lake), "build", *_module_records(identity, "tests"),
            ]),
            ("elaborate-all-standalone-lean-scripts", [
                sys.executable, "scripts/release_validation.py", "compile-lean-scripts",
                "--root", ".", "--output", str(project_build / "lib" / "lean"),
                "--lake", str(lake), "--lean", str(lean),
            ]),
        )
        for index, (name, command) in enumerate(commands):
            steps.append(run_command(
                name=name, command=command, cwd=workspace, environment=environment,
                log_path=logs / f"{index:02d}-{name}.log", output_dir=output_dir,
            ))

        review_dir = workspace / ".lake" / "offline-review"
        steps.append(run_command(
            name="generate-reviewer-workspace",
            command=[sys.executable, "scripts/reviewer_workspace.py", "--root", ".",
                     "--output", str(review_dir)],
            cwd=workspace, environment=environment,
            log_path=logs / "06-generate-reviewer-workspace.log", output_dir=output_dir,
        ))
        review_olean = review_dir / "Review.olean"
        steps.append(run_command(
            name="compile-production-axiom-review",
            command=[str(lake), "env", str(lean), str(review_dir / "Review.lean"),
                     "-o", str(review_olean)],
            cwd=workspace, environment=environment,
            log_path=logs / "07-compile-production-axiom-review.log", output_dir=output_dir,
        ))
        generated_dir = workspace / ".lake" / "offline-generated"
        generated_dir.mkdir(parents=True)
        generated_source = generated_dir / f"{GENERATED_MODULE}.lean"
        generated_source.write_text(
            render_all_production(identity["production_modules"]), encoding="utf-8"
        )
        generated_olean = project_build / "lib" / "lean" / f"{GENERATED_MODULE}.olean"
        steps.append(run_command(
            name="compile-all-production-import-root",
            command=[str(lake), "env", str(lean), str(generated_source),
                     "-o", str(generated_olean)],
            cwd=workspace, environment=environment,
            log_path=logs / "08-compile-all-production-import-root.log", output_dir=output_dir,
        ))
        steps.append(run_command(
            name="leanchecker-fresh-single-thread-replay",
            command=[str(lake), "env", str(leanchecker), "--fresh", GENERATED_MODULE],
            cwd=workspace, environment=environment,
            log_path=logs / "09-leanchecker-fresh-single-thread-replay.log",
            output_dir=output_dir,
        ))
        build_lib = project_build / "lib" / "lean"
        expected = _expected_olean_paths(identity)
        actual = {
            path.relative_to(build_lib) for path in build_lib.rglob("*.olean")
            if path.is_file() and not path.is_symlink()
        }
        if actual != expected:
            raise ReleaseValidationError(
                "offline rebuild artifact set differs from classified sources: "
                f"missing={sorted(map(str, expected - actual))[:10]}, "
                f"unexpected={sorted(map(str, actual - expected))[:10]}"
            )
        rebuilt_identity = compute_artifact_identity(project_build, workspace_packages)
        matches_validated = rebuilt_identity == receipt["artifact_identity"]
        if rebuilt_identity["package_files"] != receipt["artifact_identity"]["package_files"]:
            raise ReleaseValidationError("sealed dependency inputs changed during offline rebuild")
        if compute_release_identity(workspace) != identity:
            raise ReleaseValidationError("frozen source inputs changed during offline rebuild")
        toolchain_after = compute_toolchain_runtime_identity(bundle_root / "toolchain")
        if toolchain_after != toolchain_before:
            raise ReleaseValidationError("offline toolchain changed during rebuild")
        if (
            sha256_file(lake) != wrapper_hash
            or sha256_file(override_path) != override_hash
            or sha256_file(workspace_override) != override_hash
        ):
            raise ReleaseValidationError("offline Lake resolution inputs changed during rebuild")
        generated_artifacts = {
            "review_lean": {"path": (review_dir / "Review.lean").relative_to(workspace).as_posix(),
                            "sha256": sha256_file(review_dir / "Review.lean")},
            "theorem_map": {"path": (review_dir / "theorem-map.json").relative_to(workspace).as_posix(),
                            "sha256": sha256_file(review_dir / "theorem-map.json")},
            "review_olean": {"path": review_olean.relative_to(workspace).as_posix(),
                             "sha256": sha256_file(review_olean)},
            "all_production_source": {"path": generated_source.relative_to(workspace).as_posix(),
                                      "sha256": sha256_file(generated_source)},
            "all_production_olean": {"path": generated_olean.relative_to(workspace).as_posix(),
                                     "sha256": sha256_file(generated_olean)},
        }
    except ReleaseValidationError as error:
        failure = error
        if error.step is not None:
            steps.append(error.step)
        actual, expected, matches_validated = set(), set(), False

    report: dict[str, object] = {
        "schema_version": 1,
        "record_kind": "frozen-bundle-offline-rebuild-report",
        "success": failure is None,
        "authoritative_release_receipt": False,
        "claim": "fresh-project-rebuild-with-verified-reused-dependency-artifacts",
        "bundle_id": manifest["bundle_id"],
        "proof_identity": manifest["proof_identity"],
        "workspace_project_build_initially_absent": True,
        "dependency_artifacts_reused": True,
        "lean_num_threads": "1",
        "classified_module_counts": {
            category: len(identity["lean_source_classification"]["categories"][category])
            for category in (
                "production_certifiedjl", "production_vendor", "certifiedjl_fast",
                "tests", "scripts",
            )
        },
        "expected_olean_count": len(expected),
        "actual_olean_count": len(actual),
        "artifact_identity_matches_validated_bundle": matches_validated,
        "generated_artifacts": generated_artifacts,
        "started_utc": started,
        "finished_utc": utc_now(),
        "steps": steps,
    }
    if failure is not None:
        report["failure"] = str(failure)
    report["report_digest"] = canonical_digest(
        "CertifiedJL-frozen-bundle-offline-rebuild-v1", report
    )
    _write_new(output_dir / (REPORT_NAME if failure is None else FAILURE_NAME), report)
    if failure is not None:
        raise failure
    return report


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--bundle-dir", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args(argv)
    from proof_bundle import verify_proof_bundle

    manifest = verify_proof_bundle(
        args.archive, extract_to=args.bundle_dir, check_host=True,
    )
    report = rebuild_verified_bundle(
        args.bundle_dir, args.workspace, args.output_dir, manifest,
    )
    print(f"offline rebuild passed: {report['report_digest']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
