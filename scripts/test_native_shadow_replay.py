#!/usr/bin/env python3
"""Tests for the isolated native shadow replay planner."""

from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


sys.path.insert(0, str(Path(__file__).resolve().parent))

import native_shadow_replay as native_replay  # noqa: E402

from audit_native_replay import (  # noqa: E402
    audit as audit_native_replay,
    validate_catalog_selection,
    validate_document_identity,
)

from native_shadow_replay import (  # noqa: E402
    AUDIT_TARGETS_PER_BLOCK,
    DEFAULT_CATALOG,
    NativeReplayError,
    _verify_prior_completed_runtime,
    classify_replay_sites,
    finalize_receipt,
    import_graph,
    import_closure,
    render_axiom_audit,
    replay_build_roots,
    roots_from_catalog,
    seal_manifest,
    seal_document,
    seed_incremental_cache,
    transform_source,
    tree_digest,
    validate_production_closure,
    validate_attesting_catalog,
    validate_selection_options,
    verified_dependencies,
    validate_completed_document_chain,
    verify_document,
    verify_manifest,
    write_document,
)
from compute_replay_digest import canonical_digest


class NativeShadowReplayTests(unittest.TestCase):
    def fixture_execution(self):
        return {
            "argv": ["python3", "native_shadow_replay.py"],
            "lean_version": "Lean fixture", "lake_version": "Lake fixture",
            "os": "Fixture", "os_release": "1", "architecture": "fixture",
            "python_version": "3.11",
            "environment": {name: None for name in (
                "LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE",
                "CERTIFIEDJL_NATIVE_BUILD_DIR", "CERTIFIEDJL_NATIVE_SHADOW_DIR",
                "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS")},
            "github": {name: None for name in (
                "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_SHA", "GITHUB_REPOSITORY")},
        }

    def fixture_document_chain(
        self,
        census_sha256: str = "7" * 64,
        build_inputs: dict[str, object] | None = None,
        scope: str = "attesting",
    ):
        if build_inputs is None:
            build_inputs = {"digest": "6" * 64}
        proof = "sha256:" + "1" * 64
        procedure = "sha256:" + "2" * 64
        metadata = "sha256:" + "3" * 64
        validation = canonical_digest("CertifiedJL-validation-inputs-v2", {
            "mode": "native",
            "proof_closure_digest": proof,
            "validation_procedure_digest": procedure,
            "metadata_digest": metadata,
        })
        source = seal_document({
            "schema_version": 2,
            "identity_kind": "source-inputs",
            "attests_execution": False,
            "mode": "native",
            "source_commit": "4" * 40,
            "source_tree_digest": "sha256:" + "5" * 64,
            "proof_closure_digest": proof,
            "validation_procedure_digest": procedure,
            "metadata_digest": metadata,
            "validation_digest": validation,
            "digest": validation,
        }, "source-inputs")
        manifest = seal_document({
            "schema_version": 2,
            "mode": "native-shadow-replay",
            "execution": self.fixture_execution(),
            "attests_execution": False,
            "source_inputs_sha256": source["source_inputs_sha256"],
            "source_commit": source["source_commit"],
            "validation_scope": scope,
            "build_inputs": build_inputs,
            "incremental_cache": {"used": False},
        }, "manifest")
        provenance = seal_document({
            "schema_version": 2,
            "mode": "native-shadow-replay-provenance",
            "execution": self.fixture_execution(),
            "attests_execution": True,
            "source_inputs_sha256": source["source_inputs_sha256"],
            "transformation_manifest_sha256": manifest["manifest_sha256"],
            "source_commit": source["source_commit"],
            "validation_scope": scope,
            "build_status": 0,
            "axiom_audit_status": 0,
            "incremental_cache": {"used": False},
        }, "provenance")
        audit = seal_document({
            "schema_version": 2,
            "mode": "native-shadow-replay-independent-audit",
            "execution": self.fixture_execution(),
            "attests_execution": True,
            "success": True,
            "source_inputs_sha256": source["source_inputs_sha256"],
            "manifest_sha256": manifest["manifest_sha256"],
            "provenance_sha256": provenance["provenance_sha256"],
            "axiom_census_sha256": census_sha256,
            "build_inputs_digest": build_inputs["digest"],
            "source_commit": source["source_commit"],
            "validation_digest": source["validation_digest"],
            "validation_scope": scope,
            "attests_full_production_replay": scope == "attesting",
        }, "audit")
        receipt = seal_document({
            "schema_version": 2,
            "mode": "native-shadow-replay-receipt",
            "execution": self.fixture_execution(),
            "attests_execution": True,
            "success": True,
            "source_inputs_sha256": source["source_inputs_sha256"],
            "manifest_sha256": manifest["manifest_sha256"],
            "provenance_sha256": provenance["provenance_sha256"],
            "audit_sha256": audit["audit_sha256"],
            "axiom_census_sha256": census_sha256,
            "build_inputs_digest": build_inputs["digest"],
            "source_commit": source["source_commit"],
            "validation_digest": source["validation_digest"],
            "validation_scope": scope,
            "attests_full_production_replay": scope == "attesting",
            "incremental_cache": {"used": False},
        }, "receipt")
        return source, manifest, provenance, audit, receipt

    def write_document_chain(
        self,
        runtime: Path,
        source: dict[str, object],
        manifest: dict[str, object],
        provenance: dict[str, object],
        audit: dict[str, object],
        receipt: dict[str, object] | None,
        census: bytes,
    ) -> None:
        documents = [
            ("native-replay-source-inputs.json", source, "source-inputs"),
            ("native-replay-manifest.json", manifest, "manifest"),
            ("native-replay-provenance.json", provenance, "provenance"),
            ("native-replay-audit.json", audit, "audit"),
        ]
        if receipt is not None:
            documents.append(("native-replay-receipt.json", receipt, "receipt"))
        for name, document, kind in documents:
            write_document(runtime / name, document, kind)
        (runtime / "native-replay-axiom-census.txt").write_bytes(census)

    def test_transform_ignores_comments_and_strings(self) -> None:
        source = '''/- decide +kernel -/
namespace Fixture
def message := "decide +kernel"
theorem accepted : True := by
  -- decide +kernel
  decide +kernel
end Fixture
'''
        transformed, replacements = transform_source(source, "Fixture.lean")
        self.assertEqual(len(replacements), 1)
        self.assertIn("  native_decide", transformed)
        self.assertIn("/- decide +kernel -/", transformed)
        self.assertIn('"decide +kernel"', transformed)
        self.assertIn("-- decide +kernel", transformed)
        self.assertEqual((replacements[0].line, replacements[0].column), (6, 3))
        self.assertEqual(replacements[0].declaration, "Fixture.accepted")

    def test_transform_handles_nested_comments(self) -> None:
        source = (
            "/- outer /- decide +kernel -/ end -/\n"
            "namespace Fixture\n"
            "theorem nested : True := by decide  +kernel\n"
            "end Fixture\n"
        )
        transformed, replacements = transform_source(source, "Nested.lean")
        self.assertEqual(len(replacements), 1)
        self.assertIn("by native_decide\n", transformed)

    def test_transform_preserves_crlf_outside_exact_replay_span(self) -> None:
        source = (
            "namespace Fixture\r\n"
            "theorem accepted : True := by\r\n"
            "  decide +kernel\r\n"
            "end Fixture\r\n"
        )
        transformed, replacements = transform_source(source, "CRLF.lean")
        self.assertEqual(len(replacements), 1)
        self.assertEqual(
            transformed.encode("utf-8"),
            source.encode("utf-8").replace(b"decide +kernel", b"native_decide"),
        )

    def test_transform_rejects_nonproof_replay_token(self) -> None:
        with self.assertRaisesRegex(NativeReplayError, "not owned"):
            transform_source("namespace Fixture\n#check decide +kernel\nend Fixture\n", "Bad.lean")

    def test_composite_proof_transforms_owned_nested_site(self) -> None:
        source = '''namespace Fixture
theorem composite : True := by
  have h : True := by decide +kernel
  exact h
end Fixture
'''
        replacements, excluded = classify_replay_sites(source, "Composite.lean")
        self.assertEqual(len(replacements), 1)
        self.assertEqual(replacements[0].category, "composite-proof")
        self.assertEqual(excluded, ())
        transformed, transformed_sites = transform_source(source, "Composite.lean")
        self.assertEqual(transformed_sites, replacements)
        self.assertIn("have h : True := by native_decide", transformed)

    def test_private_proof_is_preserved_and_censused(self) -> None:
        source = '''namespace Fixture
private theorem internal : True := by
  decide +kernel
end Fixture
'''
        replacements, excluded = classify_replay_sites(source, "Private.lean")
        self.assertEqual(replacements, ())
        self.assertEqual(len(excluded), 1)
        self.assertEqual(excluded[0].reason, "private-declaration")
        transformed, _ = transform_source(source, "Private.lean")
        self.assertEqual(transformed, source)

    def test_import_closure_is_root_bounded(self) -> None:
        graph = {
            "Fixture.Root": ("Fixture.Shared", "Mathlib"),
            "Fixture.Shared": ("Fixture.Leaf",),
            "Fixture.Leaf": (),
            "Fixture.Unrelated": ("Fixture.Leaf",),
        }
        self.assertEqual(
            import_closure(graph, ("Fixture.Root",)),
            ("Fixture.Leaf", "Fixture.Root", "Fixture.Shared"),
        )
        with self.assertRaisesRegex(NativeReplayError, "no repository source"):
            import_closure(graph, ("Fixture.Missing",))

    def test_import_graph_excludes_ignored_direct_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            (root / ".gitignore").write_text("Ignored.lean\n", encoding="utf-8")
            (root / "Tracked.lean").write_text("def tracked := true\n", encoding="utf-8")
            (root / "Ignored.lean").write_text(
                "theorem ignored : True := by decide +kernel\n", encoding="utf-8"
            )
            subprocess.run(
                ["git", "add", ".gitignore", "Tracked.lean"], cwd=root, check=True
            )
            graph = import_graph(root)
            self.assertIn("Tracked", graph)
            self.assertNotIn("Ignored", graph)
            with self.assertRaisesRegex(NativeReplayError, "no repository source"):
                import_closure(graph, ("Ignored",))

    def test_manifest_digest_rejects_mutation(self) -> None:
        manifest = seal_manifest(
            {
                "schema_version": 2,
                "transformed_files": [
                    {"path": "Fixture.lean", "replacements": [{"line": 1}]}
                ],
            }
        )
        verify_manifest(manifest)
        mutated = copy.deepcopy(manifest)
        mutated["transformed_files"][0]["replacements"][0]["line"] = 2
        with self.assertRaisesRegex(NativeReplayError, "digest mismatch"):
            verify_manifest(mutated)

    def test_manifest_rejects_empty_transformation_record(self) -> None:
        manifest = seal_manifest(
            {
                "schema_version": 2,
                "transformed_files": [
                    {"path": "Fixture.lean", "replacements": []}
                ],
            }
        )
        with self.assertRaisesRegex(NativeReplayError, "unchanged"):
            verify_manifest(manifest)

    def test_document_domains_are_distinct(self) -> None:
        manifest = seal_document({"schema_version": 2}, "manifest")
        verify_document(manifest, "manifest")
        with self.assertRaisesRegex(NativeReplayError, "not a provenance"):
            verify_document(manifest, "provenance")

    def test_tree_digest_binds_mode_kind_and_symlink_target(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "fixture"
            path.write_bytes(b"same bytes")
            regular = tree_digest(root, (path,))
            os.chmod(path, 0o755)
            executable = tree_digest(root, (path,))
            self.assertNotEqual(regular, executable)
            path.unlink()
            path.symlink_to("first")
            first_link = tree_digest(root, (path,))
            path.unlink()
            path.symlink_to("second")
            second_link = tree_digest(root, (path,))
            self.assertNotEqual(executable, first_link)
            self.assertNotEqual(first_link, second_link)

    def test_completed_chain_rejects_v1_and_cross_document_mutation(self) -> None:
        source, manifest, provenance, audit, receipt = self.fixture_document_chain()
        validate_completed_document_chain(
            source_inputs=source, manifest=manifest, provenance=provenance,
            audit=audit, census_sha256="7" * 64, receipt=receipt,
        )
        old = copy.deepcopy(receipt)
        old["schema_version"] = 1
        with self.assertRaisesRegex(NativeReplayError, "receipt does not bind"):
            validate_completed_document_chain(
                source_inputs=source, manifest=manifest, provenance=provenance,
                audit=audit, census_sha256="7" * 64, receipt=old,
            )
        changed = copy.deepcopy(audit)
        changed["manifest_sha256"] = "8" * 64
        with self.assertRaisesRegex(NativeReplayError, "do not cross-bind"):
            validate_completed_document_chain(
                source_inputs=source, manifest=manifest, provenance=provenance,
                audit=changed, census_sha256="7" * 64, receipt=receipt,
            )
        partial = self.fixture_document_chain(scope="diagnostic-partial")
        validate_completed_document_chain(
            source_inputs=partial[0], manifest=partial[1], provenance=partial[2],
            audit=partial[3], census_sha256="7" * 64, receipt=partial[4],
        )
        mislabeled_audit = copy.deepcopy(partial[3])
        mislabeled_audit["attests_full_production_replay"] = True
        with self.assertRaisesRegex(NativeReplayError, "do not cross-bind"):
            validate_completed_document_chain(
                source_inputs=partial[0], manifest=partial[1], provenance=partial[2],
                audit=mislabeled_audit, census_sha256="7" * 64, receipt=partial[4],
            )
        kernel_source = copy.deepcopy(source)
        kernel_source["mode"] = "kernel"
        kernel_validation = canonical_digest("CertifiedJL-validation-inputs-v2", {
            "mode": "kernel",
            "proof_closure_digest": kernel_source["proof_closure_digest"],
            "validation_procedure_digest": kernel_source["validation_procedure_digest"],
            "metadata_digest": kernel_source["metadata_digest"],
        })
        kernel_source["validation_digest"] = kernel_validation
        kernel_source["digest"] = kernel_validation
        kernel_source = seal_document(kernel_source, "source-inputs")
        with self.assertRaisesRegex(NativeReplayError, "wrong mode"):
            validate_completed_document_chain(
                source_inputs=kernel_source, manifest=manifest, provenance=provenance,
                audit=audit, census_sha256="7" * 64, receipt=receipt,
            )

    def test_failed_finalization_leaves_no_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            runtime = Path(directory)
            with self.assertRaises(NativeReplayError):
                finalize_receipt(runtime)
            self.assertFalse((runtime / "native-replay-receipt.json").exists())

    def test_auditor_rejects_dangling_output_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            runtime = base / "runtime"
            root = base / "root"
            runtime.mkdir()
            root.mkdir()
            for filename, error in (
                ("native-replay-audit.json", "audit report already exists"),
                ("native-replay-receipt.json", "runtime with a success receipt"),
            ):
                with self.subTest(filename=filename):
                    outside = base / f"outside-{filename}"
                    output = runtime / filename
                    output.symlink_to(outside)
                    with self.assertRaisesRegex(NativeReplayError, error):
                        audit_native_replay(runtime, root)
                    self.assertTrue(output.is_symlink())
                    self.assertFalse(outside.exists())
                    output.unlink()

    def test_completed_runtime_seeds_only_a_fresh_incremental_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            prior = base / "prior"
            shadow = base / "new" / "shadow-tree"
            (prior / "shadow-tree" / ".lake" / "build").mkdir(parents=True)
            (prior / "shadow-tree" / ".lake" / "build" / "fixture.olean").write_bytes(b"cache")
            (shadow / ".lake").mkdir(parents=True)
            census = b"census\n"
            census_sha256 = hashlib.sha256(census).hexdigest()
            module = prior / "shadow-tree" / "Fixture.lean"
            config = prior / "shadow-tree" / "lean-toolchain"
            module.write_bytes(b"fixture")
            config.write_bytes(b"lean")
            build_inputs = {
                "digest": "6" * 64,
                "module_inputs": [{
                    "path": "Fixture.lean", "sha256": hashlib.sha256(b"fixture").hexdigest()
                }],
                "configuration_inputs": [{
                    "path": "lean-toolchain", "sha256": hashlib.sha256(b"lean").hexdigest()
                }],
                "dependencies": [{"name": "dep", "actual_revision": "9" * 40}],
            }
            source, manifest, provenance, audit, receipt = self.fixture_document_chain(
                census_sha256, build_inputs
            )
            self.write_document_chain(
                prior, source, manifest, provenance, audit, receipt, census
            )
            _verify_prior_completed_runtime(prior, build_inputs)

            completed_documents = (
                ("native-replay-manifest.json", "manifest", manifest),
                ("native-replay-provenance.json", "provenance", provenance),
                ("native-replay-audit.json", "audit", audit),
                ("native-replay-receipt.json", "receipt", receipt),
            )
            execution_mutations = (
                ("missing", lambda record: record.pop("execution"), "execution environment"),
                (
                    "ill-typed",
                    lambda record: record["execution"]["environment"].__setitem__(
                        "LEAN_OPTS", 0
                    ),
                    "relevant environment",
                ),
                (
                    "wrong-github-sha",
                    lambda record: record["execution"]["github"].__setitem__(
                        "GITHUB_SHA", "a" * 40
                    ),
                    "GITHUB_SHA differs",
                ),
            )
            for filename, kind, document in completed_documents:
                for mutation_name, mutate, error in execution_mutations:
                    with self.subTest(document=kind, mutation=mutation_name):
                        changed = copy.deepcopy(document)
                        mutate(changed)
                        write_document(prior / filename, seal_document(changed, kind), kind)
                        with self.assertRaisesRegex(NativeReplayError, error):
                            _verify_prior_completed_runtime(prior, build_inputs)
                        write_document(prior / filename, document, kind)

            cache = seed_incremental_cache(prior, shadow, manifest["build_inputs"])
            self.assertTrue(cache["used"])
            self.assertEqual(
                (shadow / ".lake" / "build" / "fixture.olean").read_bytes(), b"cache"
            )
            with self.assertRaisesRegex(NativeReplayError, "already contains"):
                seed_incremental_cache(prior, shadow, manifest["build_inputs"])

            module.write_bytes(b"changed")
            with self.assertRaisesRegex(NativeReplayError, "cached module input differs"):
                _verify_prior_completed_runtime(prior, build_inputs)
            module.write_bytes(b"fixture")
            config.write_bytes(b"changed")
            with self.assertRaisesRegex(NativeReplayError, "configuration differs"):
                _verify_prior_completed_runtime(prior, build_inputs)
            config.write_bytes(b"lean")
            changed_dependencies = copy.deepcopy(build_inputs)
            changed_dependencies["dependencies"] = []
            with self.assertRaisesRegex(NativeReplayError, "build inputs differ"):
                _verify_prior_completed_runtime(prior, changed_dependencies)
            build = prior / "shadow-tree" / ".lake" / "build"
            (build / "external-link").symlink_to(base / "outside")
            with self.assertRaisesRegex(NativeReplayError, "contains a symlink"):
                _verify_prior_completed_runtime(prior, build_inputs)
            (build / "external-link").unlink()
            saved_build = prior / "saved-build"
            build.rename(saved_build)
            build.symlink_to(saved_build, target_is_directory=True)
            with self.assertRaisesRegex(NativeReplayError, "no native build cache"):
                _verify_prior_completed_runtime(prior, build_inputs)
            build.unlink()
            saved_build.rename(build)
            overlap_shadow = build / "nested" / "shadow-tree"
            (overlap_shadow / ".lake").mkdir(parents=True)
            with self.assertRaisesRegex(NativeReplayError, "overlap"):
                seed_incremental_cache(prior, overlap_shadow, build_inputs)
            target_build = shadow / ".lake" / "build"
            shutil.rmtree(target_build)
            target_build.symlink_to(base / "missing-cache", target_is_directory=True)
            with self.assertRaisesRegex(NativeReplayError, "already contains"):
                seed_incremental_cache(prior, shadow, build_inputs)
            target_build.unlink()
            (prior / "native-replay-receipt.json").unlink()
            with self.assertRaisesRegex(NativeReplayError, "cannot read"):
                _verify_prior_completed_runtime(prior, build_inputs)

    def test_receipt_finalization_rechecks_shadow_and_audit_success(self) -> None:
        def prepare(base: Path, *, audit_success: bool = True):
            root = base / "root"
            runtime = base / "runtime"
            shadow = runtime / "shadow-tree"
            (shadow / ".lake" / "packages").mkdir(parents=True)
            paths = []
            for relative, payload in (
                ("lean-toolchain", b"lean"),
                ("lakefile.toml", b"lake"),
                ("lake-manifest.json", b"{}"),
            ):
                source_path = root / relative
                shadow_path = shadow / relative
                source_path.parent.mkdir(parents=True, exist_ok=True)
                shadow_path.parent.mkdir(parents=True, exist_ok=True)
                source_path.write_bytes(payload)
                shadow_path.write_bytes(payload)
                paths.append(source_path)
            build_inputs = native_replay.build_input_identity(shadow, (), (), ())
            census = b"census\n"
            census_sha256 = hashlib.sha256(census).hexdigest()
            source, _manifest, _provenance, _audit, _receipt = (
                self.fixture_document_chain(census_sha256, build_inputs)
            )
            cache = {
                "used": False,
                "trust": "no incremental project cache supplied",
                "prior_receipt_sha256": None,
                "prior_build_inputs_digest": None,
                "copy_strategy": None,
            }
            manifest = seal_document({
                "schema_version": 2,
                "mode": "native-shadow-replay",
                "execution": self.fixture_execution(),
                "attests_execution": False,
                "source_inputs_sha256": source["source_inputs_sha256"],
                "source_commit": source["source_commit"],
                "validation_scope": "attesting",
                "source_tree_sha256": native_replay.tree_digest(root, tuple(paths)),
                "shadow_tree_sha256_after_transform": native_replay.tree_digest(
                    shadow, tuple(shadow / path.relative_to(root) for path in paths)
                ),
                "dependencies": [],
                "build_roots": [],
                "closure_modules": [],
                "build_inputs": build_inputs,
                "incremental_cache": cache,
            }, "manifest")
            provenance = seal_document({
                "schema_version": 2,
                "mode": "native-shadow-replay-provenance",
                "execution": self.fixture_execution(),
                "attests_execution": True,
                "source_inputs_sha256": source["source_inputs_sha256"],
                "transformation_manifest_sha256": manifest["manifest_sha256"],
                "source_commit": source["source_commit"],
                "validation_scope": "attesting",
                "build_status": 0,
                "axiom_audit_status": 0,
                "incremental_cache": cache,
            }, "provenance")
            fake_execution = {
                "argv": ["python3", "audit_native_replay.py"], "lean_version": "Lean fixture",
                "lake_version": "Lake fixture", "os": "Fixture",
                "os_release": "1", "architecture": "fixture",
                "python_version": "3.11",
                "environment": {
                    name: None for name in (
                        "LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE",
                        "CERTIFIEDJL_NATIVE_BUILD_DIR", "CERTIFIEDJL_NATIVE_SHADOW_DIR",
                        "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS",
                    )
                },
                "github": {
                    name: None for name in (
                        "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_SHA",
                        "GITHUB_REPOSITORY",
                    )
                },
            }
            audit = seal_document({
                "schema_version": 2,
                "mode": "native-shadow-replay-independent-audit",
                "attests_execution": True,
                "attests_full_production_replay": True,
                "success": audit_success,
                "source_inputs_sha256": source["source_inputs_sha256"],
                "manifest_sha256": manifest["manifest_sha256"],
                "provenance_sha256": provenance["provenance_sha256"],
                "axiom_census_sha256": census_sha256,
                "build_inputs_digest": build_inputs["digest"],
                "source_commit": source["source_commit"],
                "validation_digest": source["validation_digest"],
                "validation_scope": "attesting",
                "execution": fake_execution,
            }, "audit")
            self.write_document_chain(
                runtime, source, manifest, provenance, audit, None, census
            )
            return root, runtime, shadow, tuple(paths), fake_execution

        for mutation in (
            "none", "shadow", "failed-audit", "dangling-receipt", "github-sha"
        ):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root, runtime, shadow, paths, execution = prepare(
                    Path(directory), audit_success=mutation != "failed-audit"
                )
                if mutation == "shadow":
                    (shadow / "lakefile.toml").write_bytes(b"mutated")
                elif mutation == "dangling-receipt":
                    (runtime / "native-replay-receipt.json").symlink_to(
                        Path(directory) / "outside-receipt.json"
                    )
                elif mutation == "github-sha":
                    execution["github"]["GITHUB_SHA"] = "a" * 40
                    audit_path = runtime / "native-replay-audit.json"
                    audit = json.loads(audit_path.read_text(encoding="utf-8"))
                    audit["execution"] = execution
                    write_document(audit_path, seal_document(audit, "audit"), "audit")
                with (
                    mock.patch.object(native_replay, "ROOT", root),
                    mock.patch.object(native_replay, "tracked_files", return_value=paths),
                    mock.patch.object(native_replay, "verified_dependencies", return_value=()),
                    mock.patch.object(
                        native_replay, "validate_source_inputs_against_checkout"
                    ),
                    mock.patch.object(
                        native_replay, "execution_environment", return_value=execution
                    ),
                ):
                    if mutation == "none":
                        receipt_path = finalize_receipt(runtime)
                        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
                        verify_document(receipt, "receipt")
                        self.assertTrue(receipt["success"])
                    else:
                        with self.assertRaises(NativeReplayError):
                            finalize_receipt(runtime)
                        receipt_path = runtime / "native-replay-receipt.json"
                        if mutation == "dangling-receipt":
                            self.assertTrue(receipt_path.is_symlink())
                            self.assertFalse((Path(directory) / "outside-receipt.json").exists())
                        else:
                            self.assertFalse(receipt_path.exists())

    def test_axiom_audit_targets_are_bounded_blocks(self) -> None:
        declarations = tuple(
            {
                "declaration": f"Fixture.check_{index}",
                "type_source_sha256": "0" * 64,
                "category": "whole-declaration",
                "transformed_site_count": 1,
            }
            for index in range(AUDIT_TARGETS_PER_BLOCK + 1)
        )
        rendered = render_axiom_audit(("Fixture.Root",), declarations)
        self.assertEqual(rendered.count("run_cmd do"), 2)
        self.assertIn(
            "(fun left right => left.toString < right.toString)", rendered
        )
        blocks = rendered.split("run_cmd do")[1:]
        self.assertEqual(blocks[0].count("(``Fixture.check_"), 256)
        self.assertEqual(blocks[1].count("(``Fixture.check_"), 1)

    def test_attesting_build_adds_production_assembly(self) -> None:
        roots = ("CertifiedJL.Certificates.Fixture",)
        self.assertEqual(replay_build_roots(roots, False), (roots, ()))
        self.assertEqual(
            replay_build_roots(roots, True),
            (("CertifiedJL", "CertifiedJL.Certificates.Fixture"), ("CertifiedJL",)),
        )

    def test_attesting_manifest_rejects_resealed_family_subset(self) -> None:
        family_ids, certificate_ids, roots = roots_from_catalog(
            DEFAULT_CATALOG, ("one-row-moderate",)
        )
        relabeled_subset = {
            "catalog": "evidence/certificates/replay-families.toml",
            "validation_scope": "attesting",
            "family_ids": list(family_ids),
            "certificate_ids": list(certificate_ids),
            "roots": list(roots),
            "assembly_roots": ["CertifiedJL"],
        }
        with self.assertRaisesRegex(NativeReplayError, "selection differs"):
            validate_catalog_selection(relabeled_subset, DEFAULT_CATALOG)

    def test_attesting_replay_rejects_alternate_catalog(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            alternate = Path(directory) / "replay-families.toml"
            alternate.write_bytes(DEFAULT_CATALOG.read_bytes())
            with self.assertRaisesRegex(NativeReplayError, "replay-families.toml"):
                validate_attesting_catalog(alternate)

    def test_auditor_rejects_resealed_schema_or_mode_mutation(self) -> None:
        for mutation in (
            {"schema_version": 1, "mode": "native-shadow-replay"},
            {"schema_version": 2, "mode": "diagnostic"},
        ):
            with self.subTest(mutation=mutation):
                with self.assertRaisesRegex(NativeReplayError, "schema or mode"):
                    validate_document_identity(
                        mutation,
                        schema_version=2,
                        mode="native-shadow-replay",
                        label="native replay manifest",
                    )

    def test_production_closure_rejects_fast_module_mutation(self) -> None:
        validate_production_closure(("CertifiedJL", "CertifiedJL.Results"))
        with self.assertRaisesRegex(NativeReplayError, "fast-assumption"):
            validate_production_closure(
                ("CertifiedJL", "CertifiedJLFast.Assumptions.Fixture")
            )

    def test_dependency_verifier_rejects_non_git_package(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            packages = root / ".lake" / "packages"
            (packages / "fixture").mkdir(parents=True)
            (root / "lake-manifest.json").write_text(
                json.dumps(
                    {
                        "packages": [
                            {
                                "name": "fixture",
                                "type": "path",
                                "rev": None,
                                "subDir": None,
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(NativeReplayError, "non-git"):
                verified_dependencies(root)

    def test_dependency_verifier_rejects_wrong_origin(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root / ".lake" / "packages" / "fixture"
            package.mkdir(parents=True)
            subprocess.run(["git", "init", "-q"], cwd=package, check=True)
            subprocess.run(
                ["git", "config", "user.email", "ci-audit@example.invalid"],
                cwd=package,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "CI Audit"],
                cwd=package,
                check=True,
            )
            (package / "README").write_text("fixture\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=package, check=True)
            subprocess.run(["git", "commit", "-qm", "fixture"], cwd=package, check=True)
            revision = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=package, text=True
            ).strip()
            subprocess.run(
                ["git", "remote", "add", "origin", "https://example.invalid/wrong"],
                cwd=package,
                check=True,
            )
            (root / "lake-manifest.json").write_text(
                json.dumps(
                    {
                        "packages": [
                            {
                                "name": "fixture",
                                "type": "git",
                                "url": "https://example.invalid/expected",
                                "rev": revision,
                                "subDir": None,
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(NativeReplayError, "origin differs"):
                verified_dependencies(root)

    def test_selection_rejects_all_families_plus_family_id(self) -> None:
        with self.assertRaisesRegex(NativeReplayError, "do not combine"):
            validate_selection_options((), ("fixture",), True)


if __name__ == "__main__":
    unittest.main()
