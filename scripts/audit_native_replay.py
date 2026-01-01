#!/usr/bin/env python3
"""Independently audit a native shadow replay manifest and provenance report."""

from __future__ import annotations

import argparse
from dataclasses import asdict
import json
import os
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))

from native_shadow_replay import (  # noqa: E402
    DEFAULT_CATALOG,
    NativeReplayError,
    ROOT,
    classify_replay_sites,
    build_input_identity,
    execution_environment,
    git_output,
    git_status,
    import_closure,
    import_graph,
    module_source,
    read_utf8_exact,
    render_axiom_audit,
    roots_from_catalog,
    sha256,
    tracked_files,
    transform_source,
    tree_digest,
    validate_execution_environment,
    validate_execution_against_current,
    validate_github_source_commit,
    validate_source_inputs_against_checkout,
    validate_production_closure,
    verified_dependencies,
    read_document,
    seal_document,
    write_document_exclusive,
)


CANONICAL_CATALOG = DEFAULT_CATALOG.relative_to(ROOT).as_posix()


def load_json(path: Path, kind: str) -> dict[str, object]:
    return read_document(path, kind)


def validate_document_identity(
    payload: dict[str, object], *, schema_version: int, mode: str, label: str
) -> None:
    if payload.get("schema_version") != schema_version or payload.get("mode") != mode:
        raise NativeReplayError(f"unsupported {label} schema or mode")


def validate_catalog_selection(
    manifest: dict[str, object], catalog_path: Path
) -> None:
    """Reconstruct and verify the catalog selection claimed by a manifest."""
    validation_scope = manifest.get("validation_scope")
    if validation_scope == "attesting":
        if manifest.get("catalog") != CANONICAL_CATALOG:
            raise NativeReplayError(
                "attesting manifest does not use the canonical replay-family catalog"
            )
        family_ids, certificate_ids, catalog_roots = roots_from_catalog(
            catalog_path, (), all_families=True
        )
    elif validation_scope == "diagnostic-partial":
        family_ids, certificate_ids, catalog_roots = roots_from_catalog(
            catalog_path, tuple(map(str, manifest.get("family_ids", [])))
        )
    else:
        raise NativeReplayError("manifest has an invalid validation scope")
    if (
        list(family_ids) != manifest.get("family_ids")
        or list(certificate_ids) != manifest.get("certificate_ids")
        or list(catalog_roots) != manifest.get("roots")
    ):
        raise NativeReplayError("manifest selection differs from replay-family catalog")


def audit(runtime: Path, root: Path = ROOT) -> None:
    manifest_path = runtime / "native-replay-manifest.json"
    provenance_path = runtime / "native-replay-provenance.json"
    census_path = runtime / "native-replay-axiom-census.txt"
    source_inputs_path = runtime / "native-replay-source-inputs.json"
    audit_report_path = runtime / "native-replay-audit.json"
    receipt_path = runtime / "native-replay-receipt.json"
    shadow = runtime.resolve() / "shadow-tree"
    if root == shadow or root in shadow.parents:
        raise NativeReplayError("shadow replay is not isolated from the source checkout")

    if receipt_path.exists() or receipt_path.is_symlink():
        raise NativeReplayError("independent audit refuses a runtime with a success receipt")
    if audit_report_path.exists() or audit_report_path.is_symlink():
        raise NativeReplayError("native replay audit report already exists")
    source_inputs = load_json(source_inputs_path, "source-inputs")
    validate_source_inputs_against_checkout(source_inputs)
    manifest = load_json(manifest_path, "manifest")
    provenance = load_json(provenance_path, "provenance")
    validate_document_identity(
        manifest,
        schema_version=2,
        mode="native-shadow-replay",
        label="native replay manifest",
    )
    validate_document_identity(
        provenance,
        schema_version=2,
        mode="native-shadow-replay-provenance",
        label="native replay provenance",
    )
    if (
        manifest.get("source_inputs_sha256") != source_inputs.get("source_inputs_sha256")
        or provenance.get("source_inputs_sha256") != source_inputs.get("source_inputs_sha256")
        or provenance.get("transformation_manifest_sha256") != manifest.get("manifest_sha256")
    ):
        raise NativeReplayError("provenance does not authenticate the transformation manifest")
    validate_execution_environment(manifest.get("execution"), "manifest")
    validate_execution_environment(provenance.get("execution"), "provenance")
    validate_execution_against_current(
        manifest.get("execution"), "manifest", "native_shadow_replay.py"
    )
    validate_github_source_commit(
        manifest.get("execution"), source_inputs.get("source_commit"), "manifest"
    )
    if provenance.get("execution") != manifest.get("execution"):
        raise NativeReplayError("provenance execution identity differs from the manifest")
    if manifest.get("production_sources_modified") is not False:
        raise NativeReplayError("manifest does not assert production byte preservation")
    if manifest.get("source_clean") is not True or manifest.get(
        "source_status_sha256"
    ) != sha256(b""):
        raise NativeReplayError("manifest was not produced from a clean source checkout")
    if git_status(root):
        raise NativeReplayError("source worktree is not clean during native audit")
    commit = git_output(root, "rev-parse", "HEAD").decode().strip()
    if manifest.get("source_commit") != commit:
        raise NativeReplayError("source commit differs from the replay manifest")
    paths = tracked_files(root)
    if manifest.get("source_tree_sha256") != tree_digest(root, paths):
        raise NativeReplayError("source tree digest differs from the replay manifest")
    dependencies = verified_dependencies(root)
    if manifest.get("dependencies") != list(dependencies):
        raise NativeReplayError("live dependency revisions differ from the replay manifest")
    source_packages = root / ".lake" / "packages"
    shadow_packages = shadow / ".lake" / "packages"
    expected_package_names = sorted(str(record["name"]) for record in dependencies)
    if not shadow_packages.is_dir() or sorted(
        path.name for path in shadow_packages.iterdir()
    ) != expected_package_names:
        raise NativeReplayError("shadow dependency package set differs from the manifest")
    for name in expected_package_names:
        shadow_package = shadow_packages / name
        source_package = source_packages / name
        if not shadow_package.is_symlink():
            raise NativeReplayError(f"shadow dependency {name} is not a symlink")
        if shadow_package.resolve() != source_package.resolve():
            raise NativeReplayError(
                f"shadow dependency {name} resolves to a different live checkout"
            )
    validation_scope = manifest.get("validation_scope")
    if validation_scope not in {"attesting", "diagnostic-partial"}:
        raise NativeReplayError("manifest has an invalid validation scope")
    catalog = manifest.get("catalog")
    if validation_scope == "attesting" and catalog != CANONICAL_CATALOG:
        raise NativeReplayError(
            "attesting manifest does not use the canonical replay-family catalog"
        )
    if catalog:
        catalog_path = (root / str(catalog)).resolve()
        if root != catalog_path and root not in catalog_path.parents:
            raise NativeReplayError("replay-family catalog escapes the source checkout")
        if manifest.get("catalog_sha256") != sha256(catalog_path.read_bytes()):
            raise NativeReplayError("replay-family catalog digest mismatch")
        validate_catalog_selection(manifest, catalog_path)
    elif manifest.get("family_ids") or manifest.get("certificate_ids"):
        raise NativeReplayError("direct-root replay contains catalog-family metadata")
    expected_assembly_roots = ["CertifiedJL"] if validation_scope == "attesting" else []
    if validation_scope == "attesting":
        source_family_ids = [
            str(record.get("id")) for record in source_inputs.get("families", [])
        ]
        if (
            source_inputs.get("certificate_ids") != manifest.get("certificate_ids")
            or source_inputs.get("replay_roots") != manifest.get("roots")
            or source_inputs.get("assembly_roots") != expected_assembly_roots
            or source_inputs.get("build_roots") != manifest.get("build_roots")
            or source_family_ids != manifest.get("family_ids")
        ):
            raise NativeReplayError(
                "attesting manifest scope differs from the full source-input identity"
            )
    if manifest.get("assembly_roots") != expected_assembly_roots:
        raise NativeReplayError("manifest assembly roots differ from validation scope")
    expected_build_roots = sorted(
        set(map(str, manifest.get("roots", []))) | set(expected_assembly_roots)
    )
    if manifest.get("build_roots") != expected_build_roots:
        raise NativeReplayError("manifest build roots are not selection-derived")
    if manifest.get("build_command") != ["lake", "build", *expected_build_roots]:
        raise NativeReplayError("manifest build command is not root-derived")
    if manifest.get("axiom_audit_command") != [
        "lake", "env", "lean", "CertifiedJLNativeReplayAudit.lean"
    ]:
        raise NativeReplayError("manifest axiom-audit command is unexpected")
    closure = import_closure(
        import_graph(root, paths), tuple(expected_build_roots)
    )
    validate_production_closure(closure)
    if list(closure) != manifest.get("closure_modules"):
        raise NativeReplayError("manifest closure differs from the repository import graph")
    expected_build_inputs = build_input_identity(
        shadow, closure, tuple(expected_build_roots), dependencies
    )
    if manifest.get("build_inputs") != expected_build_inputs:
        raise NativeReplayError("manifest build-input identity differs from the shadow closure")
    if provenance.get("build_inputs_digest") != expected_build_inputs.get("digest"):
        raise NativeReplayError("provenance build-input identity differs from the manifest")
    cache = manifest.get("incremental_cache")
    if not isinstance(cache, dict) or not isinstance(cache.get("used"), bool):
        raise NativeReplayError("manifest has invalid incremental-cache metadata")
    if provenance.get("incremental_cache") != cache:
        raise NativeReplayError("provenance incremental-cache metadata differs")
    if cache.get("used") and (
        not isinstance(cache.get("prior_receipt_sha256"), str)
        or cache.get("prior_build_inputs_digest") != expected_build_inputs.get("digest")
        or cache.get("copy_strategy") not in {
            "apfs-copy-on-write", "reflink-or-independent-copy",
            "independent-copy-fallback", "independent-copy",
        }
    ):
        raise NativeReplayError("reused cache lacks a matching prior receipt/build identity")
    if not cache.get("used") and any(
        cache.get(field) is not None
        for field in ("prior_receipt_sha256", "prior_build_inputs_digest", "copy_strategy")
    ):
        raise NativeReplayError("fresh replay incorrectly claims prior-cache metadata")
    if (
        manifest.get("fast_module_count") != 0
        or manifest.get("fast_module_policy")
        != "production native closure excludes CertifiedJLFast"
    ):
        raise NativeReplayError("manifest does not enforce the no-fast closure policy")
    if manifest.get("shadow_tree_sha256_before_transform") != manifest.get(
        "source_tree_sha256"
    ):
        raise NativeReplayError("shadow tree was not an exact source copy before transformation")

    transformed_records = {
        str(record["module"]): record
        for record in manifest.get("transformed_files", [])
    }
    if len(transformed_records) != len(manifest.get("transformed_files", [])):
        raise NativeReplayError("duplicate transformed module in manifest")
    transformed_by_path = {
        str(record["path"]): record
        for record in manifest.get("transformed_files", [])
    }
    if len(transformed_by_path) != len(transformed_records):
        raise NativeReplayError("duplicate transformed path in manifest")
    replacement_count = 0
    excluded_sites: list[dict[str, object]] = []
    for module in manifest.get("closure_modules", []):
        source_path = module_source(root, str(module))
        if not source_path.is_file():
            continue
        shadow_path = module_source(shadow, str(module))
        if not shadow_path.is_file():
            raise NativeReplayError(f"shadow closure is missing {module}")
        source = read_utf8_exact(source_path)
        shadow_source = read_utf8_exact(shadow_path)
        replacements, excluded = classify_replay_sites(source, str(module))
        transformed, transformed_replacements = transform_source(source, str(module))
        if transformed_replacements != replacements:
            raise NativeReplayError(f"inconsistent replay classification for {module}")
        excluded_sites.extend(
            {
                "module": str(module),
                "path": source_path.relative_to(root).as_posix(),
                **asdict(site),
            }
            for site in excluded
        )
        record = transformed_records.get(str(module))
        if replacements:
            if record is None:
                raise NativeReplayError(f"uncataloged transformed module {module}")
            if asdict_replacements(replacements) != record.get("replacements"):
                raise NativeReplayError(f"replacement census mismatch for {module}")
            if record.get("source_sha256") != sha256(source.encode("utf-8")):
                raise NativeReplayError(f"source hash mismatch for {module}")
            if record.get("shadow_sha256") != sha256(transformed.encode("utf-8")):
                raise NativeReplayError(f"transformed hash mismatch for {module}")
            if shadow_source != transformed:
                raise NativeReplayError(f"non-replay bytes changed in shadow module {module}")
            replacement_count += len(replacements)
        elif record is not None:
            raise NativeReplayError(f"manifest transforms a module with no replay site: {module}")
        elif shadow_source != source:
            raise NativeReplayError(f"unchanged closure module differs in shadow: {module}")
    if set(transformed_records) - set(map(str, manifest.get("closure_modules", []))):
        raise NativeReplayError("manifest transforms a module outside the selected closure")
    if replacement_count != manifest.get("replacement_count"):
        raise NativeReplayError("manifest replacement total mismatch")
    if excluded_sites != manifest.get("excluded_replay_sites"):
        raise NativeReplayError("manifest excluded-site census mismatch")
    if len(excluded_sites) != manifest.get("excluded_replay_site_count"):
        raise NativeReplayError("manifest excluded-site total mismatch")
    tracked_relatives = {path.relative_to(root).as_posix() for path in paths}
    if set(transformed_by_path) - tracked_relatives:
        raise NativeReplayError("manifest transforms an untracked shadow path")
    for source_path in paths:
        relative = source_path.relative_to(root)
        relative_string = relative.as_posix()
        shadow_path = shadow / relative
        record = transformed_by_path.get(relative_string)
        if source_path.is_symlink():
            if record is not None:
                raise NativeReplayError(
                    f"manifest attempts to transform symlink {relative_string}"
                )
            if not shadow_path.is_symlink() or os.readlink(shadow_path) != os.readlink(
                source_path
            ):
                raise NativeReplayError(
                    f"tracked shadow symlink differs at {relative_string}"
                )
            continue
        if not shadow_path.is_file() or shadow_path.is_symlink():
            raise NativeReplayError(
                f"tracked shadow file kind differs at {relative_string}"
            )
        expected_bytes = source_path.read_bytes()
        if record is not None:
            expected_source, _ = transform_source(
                expected_bytes.decode("utf-8"), str(record["module"])
            )
            expected_bytes = expected_source.encode("utf-8")
        if shadow_path.read_bytes() != expected_bytes:
            raise NativeReplayError(
                f"tracked shadow bytes differ outside exact substitutions at {relative_string}"
            )
    shadow_paths = tuple(shadow / path.relative_to(root) for path in paths)
    if manifest.get("shadow_tree_sha256_after_transform") != tree_digest(
        shadow, shadow_paths
    ):
        raise NativeReplayError("complete transformed shadow-tree digest mismatch")

    for field in ("build_status", "axiom_audit_status"):
        if provenance.get(field) != 0:
            raise NativeReplayError(f"native provenance has nonzero {field}")
    census_output = census_path.read_bytes()
    if provenance.get("axiom_audit_output_sha256") != sha256(census_output):
        raise NativeReplayError("collectAxioms output digest mismatch")
    if (
        provenance.get("source_commit") != manifest.get("source_commit")
        or provenance.get("roots") != manifest.get("roots")
        or provenance.get("build_roots") != manifest.get("build_roots")
        or provenance.get("build_command") != manifest.get("build_command")
        or provenance.get("axiom_audit_command") != manifest.get("axiom_audit_command")
        or provenance.get("assembly_roots") != manifest.get("assembly_roots")
        or provenance.get("validation_scope") != manifest.get("validation_scope")
        or provenance.get("dependencies") != manifest.get("dependencies")
        or provenance.get("declarations")
        != manifest.get("transformed_declarations")
    ):
        raise NativeReplayError("provenance metadata differs from the transformation manifest")
    expected_declarations = {
        str(record["declaration"]): record
        for record in manifest.get("transformed_declarations", [])
    }
    reconstructed_declarations: dict[str, dict[str, object]] = {}
    for transformed_file in manifest.get("transformed_files", []):
        for replacement in transformed_file.get("replacements", []):
            declaration = str(replacement["declaration"])
            record = reconstructed_declarations.setdefault(
                declaration,
                {
                    "declaration": declaration,
                    "type_source_sha256": replacement[
                        "declaration_type_source_sha256"
                    ],
                    "category": replacement["category"],
                    "transformed_site_count": 0,
                },
            )
            if (
                record["type_source_sha256"]
                != replacement["declaration_type_source_sha256"]
                or record["category"] != replacement["category"]
            ):
                raise NativeReplayError(
                    f"inconsistent replacement ownership for {declaration}"
                )
            record["transformed_site_count"] = int(
                record["transformed_site_count"]
            ) + 1
    reconstructed_list = [
        reconstructed_declarations[name] for name in sorted(reconstructed_declarations)
    ]
    if reconstructed_list != manifest.get("transformed_declarations"):
        raise NativeReplayError("transformed declaration census is not replacement-derived")
    audit_source = shadow / "CertifiedJLNativeReplayAudit.lean"
    expected_audit_source = render_axiom_audit(
        tuple(map(str, manifest.get("build_roots", []))),
        tuple(manifest.get("transformed_declarations", [])),
    )
    if not audit_source.is_file() or read_utf8_exact(audit_source) != expected_audit_source:
        raise NativeReplayError("collectAxioms audit source is not manifest-derived")
    census = provenance.get("axiom_census", [])
    census_by_declaration: dict[str, list[dict[str, object]]] = {}
    known_axioms = {str(record.get("axiom", "")) for record in census}
    if len(known_axioms) != len(census):
        raise NativeReplayError("collectAxioms census contains duplicate direct axioms")
    for record in census:
        declaration = str(record.get("declaration", ""))
        if declaration not in expected_declarations:
            raise NativeReplayError(f"collectAxioms reported unknown owner {declaration}")
        census_by_declaration.setdefault(declaration, []).append(record)
        axiom = str(record.get("axiom", ""))
        if not axiom.startswith(declaration + "._native.native_decide.ax_"):
            raise NativeReplayError(
                f"unexpected axiom ownership for {declaration}"
            )
        if not str(record.get("native_type_hash", "")).isdigit() or not str(
            record.get("axiom_type_hash", "")
        ).isdigit():
            raise NativeReplayError(
                f"missing native type census for {declaration}"
            )
        expected = expected_declarations[declaration]
        if (
            record.get("type_source_sha256") != expected.get("type_source_sha256")
            or record.get("category") != expected.get("category")
            or record.get("transformed_site_count")
            != expected.get("transformed_site_count")
            or not isinstance(record.get("direct_axiom_count"), int)
            or not str(record.get("native_proposition_hash", "")).isdigit()
        ):
            raise NativeReplayError(f"native census metadata mismatch for {declaration}")
        dependencies = record.get("collect_axioms")
        if (
            not isinstance(dependencies, list)
            or dependencies != sorted(set(map(str, dependencies)))
            or not set(map(str, dependencies)) <= known_axioms
        ):
            raise NativeReplayError(
                f"native dependency closure is incomplete for {declaration}"
            )
    for declaration, expected in expected_declarations.items():
        owned = census_by_declaration.get(declaration, [])
        category = expected.get("category")
        source_sites = expected.get("transformed_site_count")
        if (
            (category == "whole-declaration" and len(owned) != 1)
            or (
                category == "composite-proof"
                and (not isinstance(source_sites, int) or not owned)
            )
            or category not in {"whole-declaration", "composite-proof"}
            or any(record.get("direct_axiom_count") != len(owned) for record in owned)
        ):
            raise NativeReplayError(
                f"collectAxioms census count mismatch for {declaration}"
            )
        axiom_names = [str(record.get("axiom", "")) for record in owned]
        if axiom_names != sorted(set(axiom_names)):
            raise NativeReplayError(
                f"collectAxioms census is not unique and deterministic for {declaration}"
            )
        dependency_views = {
            tuple(map(str, record.get("collect_axioms", []))) for record in owned
        }
        if len(dependency_views) != 1 or not set(axiom_names) <= set(
            next(iter(dependency_views))
        ):
            raise NativeReplayError(
                f"direct native axioms are missing from the closure for {declaration}"
            )

    census_sha256 = sha256(census_output)
    audit_report = seal_document(
        {
            "schema_version": 2,
            "mode": "native-shadow-replay-independent-audit",
            "validation_scope": validation_scope,
            "attests_execution": True,
            "attests_full_production_replay": validation_scope == "attesting",
            "success": True,
            "source_inputs_sha256": source_inputs["source_inputs_sha256"],
            "manifest_sha256": manifest["manifest_sha256"],
            "provenance_sha256": provenance["provenance_sha256"],
            "axiom_census_sha256": census_sha256,
            "source_commit": source_inputs["source_commit"],
            "validation_digest": source_inputs["validation_digest"],
            "build_inputs_digest": expected_build_inputs["digest"],
            "execution": execution_environment([sys.executable, *sys.argv]),
            "self_hash_is_signature": False,
        },
        "audit",
    )
    write_document_exclusive(audit_report_path, audit_report, "audit")

    print(
        f"native replay audited: {len(manifest.get('roots', []))} roots, "
        f"{len(transformed_records)} transformed files, {replacement_count} sites, "
        f"{len(census)} exact collectAxioms/type records"
    )


def asdict_replacements(replacements: tuple[object, ...]) -> list[dict[str, object]]:
    return [asdict(replacement) for replacement in replacements]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-dir", type=Path)
    args = parser.parse_args()
    configured = args.runtime_dir or (
        Path(value) if (value := os.environ.get("CERTIFIEDJL_NATIVE_BUILD_DIR")) else None
    )
    if configured is None:
        raise NativeReplayError(
            "set CERTIFIEDJL_NATIVE_BUILD_DIR or pass --runtime-dir"
        )
    audit(configured.resolve())


if __name__ == "__main__":
    try:
        main()
    except NativeReplayError as error:
        raise SystemExit(f"native replay audit error: {error}") from error
