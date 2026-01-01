#!/usr/bin/env python3

from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

from release_validation import (
    SOURCE_MANIFEST_NAME,
    ReleaseValidationError,
    classify_lean_sources,
    compute_artifact_identity,
    compute_release_identity,
    is_release_build_artifact,
    proof_identity_projection,
    receipt_digest,
    run_release_validation,
    validation_evidence_inventory,
    verify_release_receipt,
    verify_release_receipt_document,
    write_frozen_package_source_manifest,
    write_frozen_source_manifest,
    _stop_process_group,
    _verify_dependency_records,
)


ROOT = Path(__file__).resolve().parent.parent


class ReleaseValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)

    def make_fixture(self) -> Path:
        root = self.base / "source"
        for directory in (
            "CertifiedJL/Tests", "CertifiedJLFast", "Vendor", "scripts",
            "evidence", ".lake/packages",
        ):
            (root / directory).mkdir(parents=True, exist_ok=True)
        files = {
            ".gitignore": ".lake/\n",
            "lean-toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
            "lakefile.toml": """name = "ReleaseFixture"
[[lean_lib]]
name = "CertifiedJL"
[[lean_lib]]
name = "CertifiedJLFast"
[[lean_lib]]
name = "Vendor"
""",
            "lake-manifest.json": '{"version":"1.2.0","packages":[],"name":"ReleaseFixture","lakeDir":".lake","fixedToolchain":false}\n',
            "CertifiedJL.lean": "import CertifiedJL.Result\n",
            "CertifiedJL/Result.lean": "namespace Fixture\ntheorem result : True := trivial\nend Fixture\n",
            "Vendor/V.lean": "namespace Vendor\ntheorem value : True := trivial\nend Vendor\n",
            "CertifiedJLFast.lean": "namespace Fast\ntheorem result : True := trivial\nend Fast\n",
            "CertifiedJL/Tests/Smoke.lean": "import CertifiedJL\nexample : True := Fixture.result\n",
            "scripts/Generate.lean": "def generatedValue : Nat := 1\n",
            "scripts/check_dependency_cache.py": "print('exact fixture dependencies verified')\n",
            "scripts/check_trust.py": "print('fixture production trust verified')\n",
            "scripts/reviewer_workspace.py": (ROOT / "scripts/reviewer_workspace.py").read_text(encoding="utf-8"),
            "evidence/result-catalog.toml": """[[result]]
id = "fixture"
verification_class = "kernel_checked"
lean = "Fixture.result"
lean_owner = "CertifiedJL/Result.lean"
paper_locator = "ignored locator"
""",
            "evidence/theorem-contract.toml": "schema_version = 1\n",
            "evidence/validation-roots.toml": "schema_version = 1\n",
        }
        for relative, text in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(
            ["git", "-c", "user.name=Fixture", "-c", "user.email=f@example.invalid",
             "commit", "-qm", "fixture"], cwd=root, check=True,
        )
        return root

    def test_tiny_real_release_and_evidence_tamper_rejection(self) -> None:
        root = self.make_fixture()
        output = self.base / "release-output"
        receipt = run_release_validation(root, output)
        receipt_path = output / "release-validation-receipt.json"
        self.assertTrue(receipt["success"])
        self.assertEqual(receipt["execution"]["step_count"], 11)
        self.assertEqual(
            [step["name"] for step in receipt["execution"]["steps"]][-1],
            "leanchecker-fresh-single-thread-replay",
        )
        verify_release_receipt(
            receipt_path, expected_proof_identity=compute_release_identity(root)
        )
        evidence = validation_evidence_inventory(receipt)
        self.assertGreaterEqual(len(evidence), 15)
        victim = output / evidence[0]["path"]
        victim.write_bytes(victim.read_bytes() + b"tamper")
        with self.assertRaisesRegex(ValueError, "evidence bytes differ"):
            verify_release_receipt(receipt_path)

    def test_classification_and_paper_independence(self) -> None:
        root = self.make_fixture()
        classes = classify_lean_sources(root)
        self.assertEqual({name: len(paths) for name, paths in classes.items()}, {
            "production_certifiedjl": 2, "production_vendor": 1, "tests": 1,
            "certifiedjl_fast": 1, "scripts": 1,
        })
        before = compute_release_identity(root)
        catalog = root / "evidence/result-catalog.toml"
        catalog.write_text(catalog.read_text().replace("ignored locator", "renumbered"))
        after = compute_release_identity(root)
        self.assertEqual(before, after)
        production = root / "CertifiedJL.lean"
        production.write_text(production.read_text() + "\n")
        self.assertNotEqual(
            before["proof_closure_digest"],
            compute_release_identity(root)["proof_closure_digest"],
        )

    def test_frozen_manifest_rejects_changed_and_injected_files(self) -> None:
        root = self.make_fixture()
        paths = tuple(
            root / value for value in subprocess.check_output(
                ["git", "ls-files"], cwd=root, text=True
            ).splitlines()
        )
        shutil.rmtree(root / ".git")
        write_frozen_source_manifest(root, paths, root / SOURCE_MANIFEST_NAME)
        expected = compute_release_identity(root)
        self.assertEqual(expected["identity_kind"], "release-inputs")
        injected = root / "evidence/certificate-injection.toml"
        injected.write_text("unchecked = true\n", encoding="utf-8")
        with self.assertRaisesRegex(ReleaseValidationError, "absent from frozen"):
            compute_release_identity(root)
        injected.unlink()
        (root / "CertifiedJL.lean").write_text("changed\n", encoding="utf-8")
        with self.assertRaisesRegex(ReleaseValidationError, "differs"):
            compute_release_identity(root)

    def test_artifact_identity_normalizes_package_root_symlink(self) -> None:
        physical = self.base / "dependency"
        (physical / ".lake/build/lib/lean").mkdir(parents=True)
        (physical / "Source.lean").write_text("def x := 1\n")
        (physical / "SourceAlias.lean").symlink_to("Source.lean")
        (physical / "A").mkdir()
        (physical / "A.lean").write_text("def a := 1\n")
        (physical / "A/B.lean").write_text("def b := 1\n")
        (physical / ".gitignore").write_text("widget/package-lock.json.hash\n")
        (physical / ".lake/build/lib/lean/Source.olean").write_bytes(b"olean")
        (physical / ".lake/build/lib/lean/Source.ilean").write_bytes(b"ilean")
        (physical / ".lake/build/lib/lean/Source.ir").write_bytes(b"ir")
        (physical / ".lake/build/lib/lean/Source.olean.private").write_bytes(b"private")
        (physical / ".lake/build/lib/lean/Source.trace").write_text("host=/private/tmp\n")
        (physical / ".lake/build/lib/libPlugin.so").write_bytes(b"shared")
        (physical / ".lake/build/lib/libPlugin.trace").write_text("host=/private/tmp\n")
        (physical / ".lake/build/ir").mkdir()
        (physical / ".lake/build/ir/Source.c").write_text("/* host path */\n")
        subprocess.check_call(["git", "init", "-q"], cwd=physical)
        subprocess.check_call(["git", "config", "user.name", "Release Test"], cwd=physical)
        subprocess.check_call(
            ["git", "config", "user.email", "release-test@example.invalid"], cwd=physical
        )
        subprocess.check_call(
            ["git", "add", "Source.lean", "SourceAlias.lean", "A.lean", "A/B.lean",
             ".gitignore"], cwd=physical
        )
        subprocess.check_call(["git", "commit", "-qm", "fixture"], cwd=physical)
        ignored = physical / "widget/package-lock.json.hash"
        ignored.parent.mkdir()
        ignored.write_text("ignored-v1\n")
        project = self.base / "project-build"
        (project / "lib/lean").mkdir(parents=True)
        (project / "lib/lean/Root.olean").write_bytes(b"root")
        linked = self.base / "linked-packages"
        linked.mkdir()
        (linked / "dep").symlink_to(physical, target_is_directory=True)
        original = compute_artifact_identity(project, linked)
        artifact_paths = {record["path"] for record in original["package_files"]}
        self.assertIn("packages/dep/.lake/build/lib/lean/Source.olean", artifact_paths)
        self.assertIn("packages/dep/.lake/build/lib/lean/Source.ilean", artifact_paths)
        self.assertIn("packages/dep/.lake/build/lib/lean/Source.ir", artifact_paths)
        self.assertIn("packages/dep/.lake/build/lib/libPlugin.so", artifact_paths)
        self.assertNotIn("packages/dep/.lake/build/lib/lean/Source.trace", artifact_paths)
        self.assertNotIn("packages/dep/.lake/build/lib/libPlugin.trace", artifact_paths)
        self.assertFalse(any("/.lake/build/ir/" in path for path in artifact_paths))
        ignored.write_text("ignored-v2\n")
        self.assertEqual(original, compute_artifact_identity(project, linked))

        write_frozen_package_source_manifest(physical)
        copied = self.base / "copied-packages"
        copied.mkdir()
        shutil.copytree(physical, copied / "dep", symlinks=False)
        shutil.rmtree(copied / "dep/.git")
        shutil.rmtree(copied / "dep/widget")
        self.assertEqual(
            compute_artifact_identity(project, linked),
            compute_artifact_identity(project, copied),
        )
        injected = copied / "dep/untracked-input.json"
        injected.write_text("{}\n")
        with self.assertRaisesRegex(ReleaseValidationError, "absent from frozen"):
            compute_artifact_identity(project, copied)
        injected.unlink()
        (copied / "dep/Source.lean").write_text("def x := 2\n")
        with self.assertRaisesRegex(ReleaseValidationError, "source differs"):
            compute_artifact_identity(project, copied)

        bad = self.base / "bad-dependency"
        (bad / ".lake/build/lib/lean").mkdir(parents=True)
        (bad / ".gitignore").write_text("widget/\n")
        (bad / "Alias.lean").symlink_to("widget/generated.lean")
        subprocess.check_call(["git", "init", "-q"], cwd=bad)
        subprocess.check_call(["git", "config", "user.name", "Release Test"], cwd=bad)
        subprocess.check_call(
            ["git", "config", "user.email", "release-test@example.invalid"], cwd=bad
        )
        subprocess.check_call(["git", "add", ".gitignore", "Alias.lean"], cwd=bad)
        subprocess.check_call(["git", "commit", "-qm", "fixture"], cwd=bad)
        (bad / "widget").mkdir()
        (bad / "widget/generated.lean").write_text("def injected := 1\n")
        (bad / ".lake/build/lib/lean/Alias.olean").write_bytes(b"olean")
        bad_packages = self.base / "bad-packages"
        bad_packages.mkdir()
        (bad_packages / "bad").symlink_to(bad, target_is_directory=True)
        with self.assertRaisesRegex(ReleaseValidationError, "targets an untracked file"):
            compute_artifact_identity(project, bad_packages)

    def test_release_build_artifact_projection(self) -> None:
        accepted = (
            "lib/lean/A.olean", "lib/lean/A.ilean", "lib/lean/A.olean.private",
            "lib/lean/A.olean.server", "lib/lean/A.ir", "lib/lean/A.ir.sig",
            "lib/libA.so", "lib/libA.so.1", "lib/A.dylib", "lib/A.dll",
        )
        rejected = (
            "lib/lean/A.trace", "lib/lean/A.hash", "ir/A.c", "ir/A.c.o",
            "bin/tool", "bin/tool.trace", "lib/A.trace", "lib/libA.a", "../A.olean",
        )
        for path in accepted:
            self.assertTrue(is_release_build_artifact(Path(path)), path)
        for path in rejected:
            self.assertFalse(is_release_build_artifact(Path(path)), path)

    def test_verified_dependency_status_uses_producer_digest_schema(self) -> None:
        revision = "1" * 40
        expected = [{"name": "dep", "url": "https://example.invalid/dep", "rev": revision}]
        live = [{
            "name": "dep", "type": "git",
            "expected_url": expected[0]["url"], "actual_url": expected[0]["url"],
            "expected_revision": revision, "actual_revision": revision,
            "status_sha256": "e3b0c44298fc1c149afbf4c8996fb924"
                             "27ae41e4649b934ca495991b7852b855",
        }]
        _verify_dependency_records(live, expected)
        live[0]["status_sha256"] = "sha256:" + str(live[0]["status_sha256"])
        with self.assertRaisesRegex(ValueError, "dependency is not exact"):
            _verify_dependency_records(live, expected)

    def test_process_group_cleanup_stops_child_and_grandchild(self) -> None:
        child_pid_file = self.base / "child-pid"
        grandchild_code = (
            "import os,pathlib,signal,time; "
            "signal.signal(signal.SIGINT, signal.SIG_IGN); "
            f"pathlib.Path({str(child_pid_file)!r}).write_text(str(os.getpid())); "
            "time.sleep(60)"
        )
        parent_code = (
            "import subprocess,sys,time; "
            f"subprocess.Popen([sys.executable, '-c', {grandchild_code!r}]); "
            "time.sleep(60)"
        )
        parent = subprocess.Popen(
            [sys.executable, "-c", parent_code],
            start_new_session=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        deadline = time.monotonic() + 5
        while not child_pid_file.is_file() and time.monotonic() < deadline:
            time.sleep(0.02)
        self.assertTrue(child_pid_file.is_file())
        child_pid = int(child_pid_file.read_text())
        _stop_process_group(parent)
        self.assertIsNotNone(parent.poll())
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            try:
                os.kill(child_pid, 0)
            except ProcessLookupError:
                break
            time.sleep(0.02)
        else:
            self.fail("grandchild survived process-group cleanup")

    def test_receipt_tampering_and_proof_projection_are_rejected(self) -> None:
        # Exercise self-digest and expected-proof checks without another Lean run.
        root = self.make_fixture()
        output = self.base / "release-output"
        receipt = run_release_validation(root, output)
        projected = proof_identity_projection(receipt["source_identity"])
        verify_release_receipt_document(receipt, expected_proof_identity=projected)
        tampered = copy.deepcopy(receipt)
        tampered["execution"]["steps"][-1]["command"][-2] = "--not-fresh"
        with self.assertRaisesRegex(ValueError, "self-digest"):
            verify_release_receipt_document(tampered)
        substituted = copy.deepcopy(receipt)
        substituted["source_identity"]["proof_inputs"][0]["sha256"] = "sha256:" + "0" * 64
        substituted["receipt_digest"] = receipt_digest(substituted)
        with self.assertRaisesRegex(ValueError, "proof identity digest"):
            verify_release_receipt_document(substituted)


if __name__ == "__main__":
    unittest.main()
