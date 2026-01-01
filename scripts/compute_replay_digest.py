#!/usr/bin/env python3
"""Describe replay inputs; this document never attests successful execution."""

from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
import copy
import re
from pathlib import Path
import subprocess

from check_replay_families import validate as validate_replay_families
from lean_source import imports_in_source


ROOT = Path(__file__).resolve().parent.parent
FAMILIES = ROOT / "evidence/certificates/replay-families.toml"
CATALOG_PATH = "evidence/certificates/public-results.toml"
BUILD_CONFIGURATION = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
# Explicit exclusions: new/unrecognized fields stay bound by default.
DESCRIPTIVE_CERTIFICATE_FIELDS = frozenset({"sample_rationale", "parameters"})
PROCEDURAL_CERTIFICATE_FIELDS = frozenset({
    "generator", "generator_version", "regenerate", "sample_modules", "status",
    "fast_module", "fast_declaration", "fast_type", "fast_axioms",
})

try:
    import tomllib
except ModuleNotFoundError as exc:  # pragma: no cover
    raise SystemExit("Python 3.11 or newer is required") from exc


def module_name(source: Path) -> str:
    return ".".join(source.relative_to(ROOT).with_suffix("").parts)


def module_source(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def tracked_sources() -> set[Path]:
    payload = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT)
    return {ROOT / part.decode("utf-8") for part in payload.split(b"\0") if part}


def import_graph(paths: set[Path] | None = None) -> dict[str, tuple[str, ...]]:
    graph: dict[str, tuple[str, ...]] = {}
    for source in sorted(tracked_sources() if paths is None else paths):
        if source.suffix != ".lean":
            continue
        if source.is_symlink():
            raise SystemExit(f"replay Lean source must not be a symlink: {source}")
        graph[module_name(source)] = imports_in_source(
            source.read_text(encoding="utf-8"), str(source.relative_to(ROOT))
        )
    return graph


def closure(graph: dict[str, tuple[str, ...]], roots: set[str]) -> set[str]:
    reached: set[str] = set()
    pending = deque(sorted(roots))
    while pending:
        module = pending.popleft()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(graph.get(module, ()))
    return reached


def replay_roots(families: list[dict[str, object]]) -> set[str]:
    # Source identity is meaningful only after the topology has been checked
    # against every certificate's canonical full-replay root.  Do not hash a
    # merely parseable but incomplete or broadened catalog.
    return {
        str(root)
        for family in families
        for root in family.get("replay_roots", [])
    }


def digest_files(domain: bytes, paths: set[Path], root: Path = ROOT) -> str:
    digest = hashlib.sha256(domain + b"\0")
    for path in sorted(paths):
        relative = path.relative_to(root).as_posix().encode()
        if path.is_symlink():
            payload = b"120000\0" + path.readlink().as_posix().encode()
        else:
            mode = b"100755\0" if path.stat().st_mode & 0o111 else b"100644\0"
            payload = mode + path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def tracked_validation_inputs() -> set[Path]:
    """Return tracked non-Lean inputs consumed by replay validation."""
    payload = subprocess.run(
        [
            "git",
            "ls-files",
            "-z",
            "--",
            "evidence",
            "paper/artifact",
            "paper/generated/formalization-table.tex",
        ],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    return {
        ROOT / part.decode("utf-8")
        for part in payload.split(b"\0")
        if part and (ROOT / part.decode("utf-8")).is_file()
    }


def require_clean_source() -> None:
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    if status:
        raise SystemExit("replay source identity requires a clean source checkout")


def canonical_digest(domain: str, payload: object) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"),
                         ensure_ascii=False, allow_nan=False).encode("utf-8")
    return "sha256:" + hashlib.sha256(domain.encode() + b"\0" + encoded).hexdigest()


def catalog_projection(catalog: dict, *, mathematical: bool) -> dict:
    result = copy.deepcopy(catalog)
    excluded = DESCRIPTIVE_CERTIFICATE_FIELDS
    if mathematical:
        excluded = excluded | PROCEDURAL_CERTIFICATE_FIELDS
        result.pop("fast_result", None)
    for entry in result.get("certificate", []):
        for field in excluded:
            entry.pop(field, None)
    if mathematical:
        result["certificate"] = sorted(result.get("certificate", []),
                                       key=lambda record: record["id"])
    return result


def input_identities(
    *, root: Path, mode: str, proof_files: set[Path],
    procedure_files: set[Path], metadata_files: set[Path],
    catalog: dict, families: list[dict],
) -> dict[str, str]:
    """Pure, separately testable partition; all digests are input identities."""
    if mode not in {"kernel", "native"}:
        raise ValueError(f"unsupported replay mode: {mode}")
    normalized_families = [
        {**record, "certificate_ids": sorted(record["certificate_ids"]),
         "replay_roots": sorted(record["replay_roots"])}
        for record in sorted(families, key=lambda record: record["id"])
    ]
    proof = canonical_digest("CertifiedJL-proof-closure-v2", {
        "files": digest_files(b"CertifiedJL-proof-files-v2", proof_files, root),
        "catalog": catalog_projection(catalog, mathematical=True),
        "families": normalized_families,
        "assembly_roots": ["CertifiedJL"],
    })
    procedure = canonical_digest("CertifiedJL-validation-procedure-v2", {
        "mode": mode,
        "files": digest_files(b"CertifiedJL-procedure-files-v2", procedure_files, root),
        "catalog": {
            "fast_result": catalog.get("fast_result", []),
            "certificate": sorted([
                {key: value for key, value in entry.items()
                 if key == "id" or key in PROCEDURAL_CERTIFICATE_FIELDS}
                for entry in catalog.get("certificate", [])
            ], key=lambda record: record["id"]),
        },
    })
    metadata = "sha256:" + digest_files(
        b"CertifiedJL-descriptive-metadata-v2", metadata_files, root)
    complete = canonical_digest("CertifiedJL-validation-inputs-v2", {
        "mode": mode, "proof_closure_digest": proof,
        "validation_procedure_digest": procedure, "metadata_digest": metadata,
    })
    return {
        "proof_closure_digest": proof,
        "validation_procedure_digest": procedure,
        "metadata_digest": metadata,
        "validation_digest": complete,
        "digest": complete,
    }


def validate_identity_document(report: dict) -> None:
    """Reject success claims, wrong modes and internally inconsistent v2 inputs.

    This checks structure, not authenticity. A receipt verifier must also bind
    this document to its checkout or trusted workflow artifact provenance.
    """
    if (report.get("schema_version") != 2
            or report.get("identity_kind") != "source-inputs"
            or report.get("attests_execution") is not False
            or report.get("mode") not in {"kernel", "native"}):
        raise ValueError("expected a schema-v2 replay source-input identity")
    for field in ("proof_closure_digest", "validation_procedure_digest",
                  "metadata_digest", "validation_digest", "source_tree_digest"):
        if not isinstance(report.get(field), str) or re.fullmatch(
                r"sha256:[0-9a-f]{64}", report[field]) is None:
            raise ValueError(f"invalid replay identity {field}")
    commit = report.get("source_commit")
    if not isinstance(commit, str) or re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", commit) is None:
        raise ValueError("invalid replay identity source_commit")
    expected = canonical_digest("CertifiedJL-validation-inputs-v2", {
        "mode": report["mode"],
        "proof_closure_digest": report["proof_closure_digest"],
        "validation_procedure_digest": report["validation_procedure_digest"],
        "metadata_digest": report["metadata_digest"],
    })
    if report["validation_digest"] != expected or report.get("digest") != expected:
        raise ValueError("inconsistent replay validation identity")


def require_tracked_authorities(tracked: set[Path], root: Path = ROOT) -> None:
    for relative in (*BUILD_CONFIGURATION, CATALOG_PATH,
                     "evidence/certificates/replay-families.toml",
                     "evidence/validation-roots.toml"):
        path = root / relative
        if path not in tracked or not path.is_file() or path.is_symlink():
            raise SystemExit(f"replay authority must be a tracked regular file: {relative}")


def require_tracked_closure(modules: set[str], roots: set[str],
                            tracked: set[Path], root: Path = ROOT) -> None:
    def source(name: str) -> Path:
        return root / (name.replace(".", "/") + ".lean")
    missing = sorted(name for name in modules
        if source(name) not in tracked
        and (name in roots or name.split(".")[0] in {"CertifiedJL", "Vendor"}
             or source(name).exists()))
    if missing:
        raise SystemExit(f"replay closure requires tracked repository sources: {missing}")


def compute_identity(*, mode: str) -> dict:
    require_clean_source()
    commit_before = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    tracked = tracked_sources()
    require_tracked_authorities(tracked, ROOT)
    tree_before = digest_files(b"CertifiedJL-source-snapshot-v2", tracked, ROOT)
    families = validate_replay_families()
    certificate_ids = {
        str(certificate_id) for family in families
        for certificate_id in family.get("certificate_ids", [])
    }
    registered_roots = replay_roots(families)
    roots = registered_roots | {"CertifiedJL"}
    modules = closure(import_graph(tracked), roots)
    require_tracked_closure(modules, roots, tracked, ROOT)
    proof_files = {
        module_source(module) for module in modules if module_source(module) in tracked
    }
    for relative in BUILD_CONFIGURATION:
        path = ROOT / relative
        if not path.is_file():
            raise SystemExit(f"missing replay build configuration: {relative}")
        proof_files.add(path)

    catalog_path = ROOT / CATALOG_PATH
    with catalog_path.open("rb") as stream:
        catalog = tomllib.load(stream)
    validation_inputs = tracked_validation_inputs()
    procedure_files = {
        path for path in tracked
        if (path.relative_to(ROOT).parts[0] == "scripts"
            or path.relative_to(ROOT).parts[:2] == (".github", "workflows")
            or path.relative_to(ROOT).parts[:2] == ("paper", "artifact"))
    }
    procedure_files.add(ROOT / "evidence/validation-roots.toml")
    # Catalog prose, status reports and paper artifacts remain byte-bound in
    # the complete validation identity, separate from the validator procedure.
    metadata_files = {
        path for path in tracked
        if path.relative_to(ROOT).parts[0] in {"evidence", "paper", "docs"}
    } - procedure_files - proof_files
    identities = input_identities(
        root=ROOT, mode=mode, proof_files=proof_files,
        procedure_files=procedure_files, metadata_files=metadata_files,
        catalog=catalog, families=families,
    )
    with (ROOT / "lake-manifest.json").open("rb") as stream:
        manifest = json.load(stream)
    mathlib = next(package for package in manifest.get("packages", [])
                   if package.get("name") == "mathlib")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    require_clean_source()
    commit_after = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if (commit_after != commit_before or tracked_sources() != tracked
            or digest_files(b"CertifiedJL-source-snapshot-v2", tracked, ROOT) != tree_before):
        raise SystemExit("source snapshot changed while computing replay identity")
    return {
        "schema_version": 2,
        "identity_kind": "source-inputs",
        "attests_execution": False,
        "mode": mode,
        "source_commit": commit_before,
        "source_tree_digest": "sha256:" + tree_before,
        "lean_toolchain": toolchain,
        "mathlib_revision": mathlib.get("rev"),
        **identities,
        "families": sorted(families, key=lambda record: record["id"]),
        "certificate_ids": sorted(certificate_ids),
        "replay_roots": sorted(registered_roots),
        "assembly_roots": ["CertifiedJL"],
        "build_roots": sorted(roots),
        "family_count": len(families),
        "certificate_count": len(certificate_ids),
        "replay_root_count": len(registered_roots),
        "root_count": len(roots),
        "module_count": len(modules),
        "proof_file_count": len(proof_files),
        "validation_input_count": len(validation_inputs),
        "validation_file_count": len(proof_files | procedure_files | metadata_files),
        "procedure_file_count": len(procedure_files),
        "metadata_file_count": len(metadata_files),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("native", "kernel"), required=True)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = compute_identity(mode=args.mode)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for key, value in report.items():
            print(f"{key}={value}")


if __name__ == "__main__":
    main()
