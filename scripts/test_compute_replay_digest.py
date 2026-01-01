#!/usr/bin/env python3

from __future__ import annotations

import unittest
import tempfile
from pathlib import Path
import copy
import subprocess
import json
import compute_replay_digest as replay
from unittest.mock import Mock, patch

from compute_replay_digest import (ROOT, require_clean_source, tracked_validation_inputs, input_identities, import_graph, validate_identity_document, require_tracked_authorities, require_tracked_closure, BUILD_CONFIGURATION, CATALOG_PATH)


class ReplayDigestTests(unittest.TestCase):
    def test_validation_digest_covers_catalogs_and_generator_inputs(self) -> None:
        inputs = tracked_validation_inputs()
        for relative in (
            "evidence/result-catalog.toml",
            "evidence/theorem-contract.toml",
            "evidence/certificates/public-results.toml",
            "evidence/validation-roots.toml",
            "paper/artifact/lower-gap/verify_512_192_threshold_76_counterexample.py",
        ):
            with self.subTest(relative=relative):
                self.assertIn(ROOT / relative, inputs)

    def test_attestation_digest_rejects_dirty_source(self) -> None:
        completed = Mock(stdout=b" M theorem.lean\n")
        with patch("compute_replay_digest.subprocess.run", return_value=completed):
            with self.assertRaisesRegex(SystemExit, "clean source checkout"):
                require_clean_source()


class IdentityPartitionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.proof = self.root / "Proof.lean"
        self.procedure = self.root / "validate.py"
        self.metadata = self.root / "catalog.toml"
        self.proof.write_text("theorem t : True := True.intro\n")
        self.procedure.write_text("check_all_roots()\n")
        self.metadata.write_text('sample_rationale = "old"\n')
        self.catalog = {"schema_version": 1, "certificate": [{
            "id": "c", "contract": "t", "payload_hash": "abc",
            "production_axioms": ["propext"], "sample_rationale": "old",
            "sample_modules": ["Sample"], "full_replay": "lake build Proof",
        }]}
        self.families = [{"id": "f", "certificate_ids": ["c"],
                          "replay_roots": ["Proof"]}]

    def identity(self, mode="kernel"):
        return input_identities(root=self.root, mode=mode,
            proof_files={self.proof}, procedure_files={self.procedure},
            metadata_files={self.metadata}, catalog=self.catalog,
            families=self.families)

    def test_prose_only_changes_full_identity_not_math_or_procedure(self):
        before = self.identity()
        self.catalog["certificate"][0]["sample_rationale"] = "new"
        self.metadata.write_text('sample_rationale = "new"\n')
        after = self.identity()
        for key in ("proof_closure_digest", "validation_procedure_digest"):
            self.assertEqual(before[key], after[key])
        for key in ("metadata_digest", "validation_digest", "digest"):
            self.assertNotEqual(before[key], after[key])

    def test_proof_source_changes_mathematical_and_full_identity(self):
        before = self.identity()
        self.proof.write_text("theorem t : False := by contradiction\n")
        after = self.identity()
        self.assertNotEqual(before["proof_closure_digest"], after["proof_closure_digest"])
        self.assertNotEqual(before["digest"], after["digest"])

    def test_procedure_changes_do_not_claim_new_mathematics(self):
        before = self.identity()
        self.procedure.write_text("check_one_root()\n")
        after = self.identity()
        self.assertEqual(before["proof_closure_digest"], after["proof_closure_digest"])
        self.assertNotEqual(before["validation_procedure_digest"], after["validation_procedure_digest"])
        self.assertNotEqual(before["digest"], after["digest"])

    def test_semantic_and_unknown_fields_remain_bound(self):
        for field, value in (("contract", "other"), ("payload_hash", "bad"),
                             ("production_axioms", ["sorryAx"]),
                             ("future_security_field", "changed")):
            with self.subTest(field=field):
                old = copy.deepcopy(self.catalog)
                before = self.identity()
                self.catalog["certificate"][0][field] = value
                self.assertNotEqual(before["proof_closure_digest"], self.identity()["proof_closure_digest"])
                self.catalog = old

    def test_sampling_changes_procedure_but_not_mathematics(self):
        before = self.identity()
        self.catalog["certificate"][0]["sample_modules"] = []
        after = self.identity()
        self.assertEqual(before["proof_closure_digest"], after["proof_closure_digest"])
        self.assertNotEqual(before["validation_procedure_digest"], after["validation_procedure_digest"])

    def test_root_selection_is_bound(self):
        before = self.identity()
        self.families[0]["replay_roots"] = []
        self.assertNotEqual(before["proof_closure_digest"], self.identity()["proof_closure_digest"])

    def test_kernel_and_native_never_share_validation_identity(self):
        kernel, native = self.identity(), self.identity("native")
        self.assertEqual(kernel["proof_closure_digest"], native["proof_closure_digest"])
        self.assertNotEqual(kernel["validation_procedure_digest"], native["validation_procedure_digest"])
        self.assertNotEqual(kernel["digest"], native["digest"])

    def test_paths_are_bound_even_when_file_bytes_match(self):
        before = self.identity()
        moved = self.root / "Other.lean"
        self.proof.rename(moved)
        self.proof = moved
        self.assertNotEqual(before["proof_closure_digest"], self.identity()["proof_closure_digest"])

    def test_family_and_root_set_order_does_not_change_mathematics(self):
        self.families = [{"id": "z", "certificate_ids": ["b", "a"],
                          "replay_roots": ["Y", "X"]},
                         {"id": "a", "certificate_ids": ["c"],
                          "replay_roots": ["Z"]}]
        before = self.identity()
        self.families.reverse()
        self.families[1]["certificate_ids"].reverse()
        self.families[1]["replay_roots"].reverse()
        self.assertEqual(before["proof_closure_digest"], self.identity()["proof_closure_digest"])

    def test_build_configuration_is_mathematical_input(self):
        config = self.root / "lean-toolchain"
        config.write_text("leanprover/lean4:v4.33.1\n")
        self.proof = config
        before = self.identity()
        config.write_text("leanprover/lean4:v4.33.2\n")
        self.assertNotEqual(before["proof_closure_digest"], self.identity()["proof_closure_digest"])

    def test_import_graph_uses_only_tracked_files(self):
        tracked = self.root / "Tracked.lean"
        ignored = self.root / "Ignored.lean"
        tracked.write_text("import Ignored\n")
        ignored.write_text("axiom unchecked : False\n")
        with patch("compute_replay_digest.ROOT", self.root), patch(
                "compute_replay_digest.tracked_sources", return_value={tracked}):
            graph = import_graph()
        self.assertEqual(graph, {"Tracked": ("Ignored",)})

    def test_lean_symlink_input_is_rejected(self):
        link = self.root / "Linked.lean"
        link.symlink_to(self.proof)
        with patch("compute_replay_digest.ROOT", self.root):
            with self.assertRaisesRegex(SystemExit, "symlink"):
                import_graph({link})

    def test_source_identity_is_never_a_success_receipt(self):
        report = {**self.identity(), "schema_version": 2,
                  "identity_kind": "source-inputs", "attests_execution": False,
                  "mode": "kernel", "source_commit": "a" * 40,
                  "source_tree_digest": "sha256:" + "b" * 64}
        validate_identity_document(report)
        for field, value in (("attests_execution", True), ("schema_version", 1),
                             ("mode", "native"), ("source_commit", "main"),
                             ("metadata_digest", "sha256:" + "0" * 64)):
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_identity_document({**report, field: value})

    def test_executable_mode_is_bound(self):
        self.procedure.chmod(0o644)
        before = self.identity()
        self.procedure.chmod(0o755)
        after = self.identity()
        self.assertEqual(before["proof_closure_digest"], after["proof_closure_digest"])
        self.assertNotEqual(before["validation_procedure_digest"], after["validation_procedure_digest"])

    def test_all_canonical_authorities_must_be_tracked_regular_files(self):
        paths = {self.root / relative for relative in (*BUILD_CONFIGURATION,
            CATALOG_PATH, "evidence/certificates/replay-families.toml",
            "evidence/validation-roots.toml")}
        for path in paths:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("fixture\n")
        require_tracked_authorities(paths, self.root)
        for path in paths:
            with self.subTest(path=path), self.assertRaisesRegex(SystemExit, "tracked regular"):
                require_tracked_authorities(paths - {path}, self.root)

    def test_ignored_imported_lean_is_rejected_by_closure(self):
        ignored = self.root / "Ignored.lean"
        ignored.write_text("axiom unchecked : False\n")
        with self.assertRaisesRegex(SystemExit, "tracked repository"):
            require_tracked_closure({"Proof", "Ignored"}, {"Proof"},
                                    {self.proof}, self.root)
        with self.assertRaisesRegex(SystemExit, "tracked repository"):
            require_tracked_closure({"CertifiedJL.Missing"}, set(), set(), self.root)

    def test_unknown_mode_rejected(self):
        with self.assertRaises(ValueError):
            self.identity("fast")


class SnapshotTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        files = {
            "CertifiedJL.lean": "import Proof\n",
            "Proof.lean": "theorem t : True := True.intro\n",
            "lean-toolchain": "leanprover/lean4:v4.33.1\n",
            "lakefile.toml": 'name = "Fixture"\n',
            "lake-manifest.json": json.dumps({"packages": [{"name": "mathlib", "rev": "a" * 40}]}),
            CATALOG_PATH: 'schema_version = 1\n[[certificate]]\nid = "c"\n',
            "evidence/certificates/replay-families.toml": 'schema_version = 1\n',
            "evidence/validation-roots.toml": 'schema_version = 1\n',
            "scripts/nested/check": "check everything\n",
            ".github/workflows/test.yaml": "fixture: true\n",
            "paper/artifact/check.py": "check_reference()\n",
            ".gitignore": "Ignored.lean\n",
        }
        for relative, content in files.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        self.git("init", "-q")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "user.name", "Fixture")
        self.commit()
        self.addCleanup(patch.stopall)
        patch("compute_replay_digest.ROOT", self.root).start()
        patch("compute_replay_digest.FAMILIES", self.root / "evidence/certificates/replay-families.toml").start()
        patch("compute_replay_digest.validate_replay_families", return_value=[{
            "id": "f", "certificate_ids": ["c"], "replay_roots": ["Proof"]}]).start()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, stderr=subprocess.DEVNULL)

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")

    def test_recursive_extensionless_and_paper_tools_are_procedural(self):
        before = replay.compute_identity(mode="kernel")
        for relative in ("scripts/nested/check", ".github/workflows/test.yaml", "paper/artifact/check.py"):
            with self.subTest(path=relative):
                path = self.root / relative
                path.write_text(path.read_text() + "changed\n")
                self.commit()
                after = replay.compute_identity(mode="kernel")
                self.assertEqual(before["proof_closure_digest"], after["proof_closure_digest"])
                self.assertNotEqual(before["validation_procedure_digest"], after["validation_procedure_digest"])
                before = after

    def test_ignored_import_is_rejected_end_to_end(self):
        (self.root / "Proof.lean").write_text("import Ignored\n")
        self.commit()
        (self.root / "Ignored.lean").write_text("axiom unchecked : False\n")
        with self.assertRaisesRegex(SystemExit, "tracked repository"):
            replay.compute_identity(mode="kernel")

    def test_dirty_change_during_hashing_is_rejected(self):
        original = replay.input_identities
        def mutate(**kwargs):
            result = original(**kwargs)
            (self.root / "Proof.lean").write_text("changed\n")
            return result
        with patch("compute_replay_digest.input_identities", side_effect=mutate):
            with self.assertRaisesRegex(SystemExit, "clean source"):
                replay.compute_identity(mode="kernel")

    def test_committed_change_during_hashing_is_rejected(self):
        original = replay.input_identities
        def mutate(**kwargs):
            result = original(**kwargs)
            (self.root / "Proof.lean").write_text("changed\n")
            self.commit()
            return result
        with patch("compute_replay_digest.input_identities", side_effect=mutate):
            with self.assertRaisesRegex(SystemExit, "snapshot changed"):
                replay.compute_identity(mode="kernel")


if __name__ == "__main__":
    unittest.main()
