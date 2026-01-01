#!/usr/bin/env python3

from __future__ import annotations

import copy
from contextlib import contextmanager
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tarfile
import tempfile
import tracemalloc
import types
import unittest
from unittest import mock

import proof_bundle as bundle


class FakeReleaseValidation:
    @staticmethod
    def is_release_build_artifact(relative: Path) -> bool:
        return (
            relative.parts[:2] == ("lib", "lean")
            and str(relative).endswith(
                (".olean", ".ilean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
            )
        ) or (
            relative.parts[:1] == ("lib",) and relative.parts[:2] != ("lib", "lean")
            and (str(relative).endswith((".dylib", ".dll", ".so")) or ".so." in relative.name)
        )

    @staticmethod
    def write_frozen_source_manifest(root: Path, paths, output: Path) -> dict[str, object]:
        records = [{
            "path": path.relative_to(root).as_posix(),
            "size_bytes": path.stat().st_size,
            "sha256": bundle.sha256_file(path),
        } for path in paths]
        manifest: dict[str, object] = {
            "schema_version": 1, "record_kind": "release-source-manifest",
            "files": sorted(records, key=lambda value: value["path"]),
        }
        manifest["manifest_digest"] = bundle.canonical_digest("fixture-source-manifest", manifest)
        output.write_text(json.dumps(manifest), encoding="utf-8")
        return manifest

    @staticmethod
    def write_frozen_package_source_manifest(
        package_root: Path, output: Path | None = None,
    ) -> dict[str, object]:
        output = output or package_root / ".lake/release-package-source-manifest.json"
        records = []
        for raw in subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=package_root,
        ).split(b"\0"):
            if raw:
                relative = Path(os.fsdecode(raw))
                path = (package_root / relative).resolve()
                records.append({
                    "path": relative.as_posix(), "size_bytes": path.stat().st_size,
                    "sha256": bundle.sha256_file(path),
                })
        document = {"files": sorted(records, key=lambda value: value["path"])}
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(document))
        return document

    @staticmethod
    def compute_release_identity(root: Path) -> dict[str, object]:
        proof_files = ["Main.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]
        proof_inventory = [{
            "path": name,
            "sha256": bundle.sha256_file(root / name),
            "size": (root / name).stat().st_size,
        } for name in proof_files]
        procedure = root / "scripts" / "reviewer_workspace.py"
        procedure_inventory = [{
            "path": "scripts/reviewer_workspace.py",
            "sha256": bundle.sha256_file(procedure),
            "size": procedure.stat().st_size,
        }]
        proof_digest = bundle.canonical_digest("fixture-proof", proof_inventory)
        procedure_digest = bundle.canonical_digest("fixture-procedure", procedure_inventory)
        return {
            "schema_version": 1,
            "identity_kind": "release-inputs",
            "mode": "release",
            "proof_closure_digest": proof_digest,
            "validation_procedure_digest": procedure_digest,
            "validation_digest": bundle.canonical_digest(
                "fixture-release", [proof_digest, procedure_digest],
            ),
            "proof_inventory": proof_inventory,
            "procedure_inventory": procedure_inventory,
        }

    @staticmethod
    def proof_identity_projection(identity: dict[str, object]) -> dict[str, object]:
        return {
            "schema_version": 1,
            "identity_kind": "proof-bundle-inputs",
            "proof_closure_digest": identity["proof_closure_digest"],
            "proof_inventory": identity["proof_inventory"],
        }

    @staticmethod
    def compute_artifact_identity(project_build: Path, packages_root: Path) -> dict[str, object]:
        records: list[dict[str, object]] = []
        roots = [("project-build", project_build)]
        def add(prefix: str, root: Path, path: Path, logical: Path | None = None) -> None:
            records.append({
                "path": f"{prefix}/{(logical or path.relative_to(root)).as_posix()}",
                "sha256": bundle.sha256_file(path),
                "size": path.stat().st_size,
            })
        def add_build(prefix: str, build: Path) -> None:
            for current, _directories, files in os.walk(build):
                for name in files:
                    path = Path(current) / name
                    relative = path.relative_to(build)
                    if FakeReleaseValidation.is_release_build_artifact(relative):
                        add(prefix, build, path.resolve(), relative)
        for prefix, root in roots:
            add_build(prefix, root)
        for package in sorted(packages_root.iterdir(), key=lambda path: path.name):
            root = package.resolve()
            if (root / ".git").exists():
                relative_paths = [Path(os.fsdecode(raw)) for raw in subprocess.check_output(
                    ["git", "ls-files", "-z"], cwd=root,
                ).split(b"\0") if raw]
            else:
                frozen = json.loads(
                    (root / ".lake/release-package-source-manifest.json").read_text()
                )
                relative_paths = [Path(record["path"]) for record in frozen["files"]]
            for relative in relative_paths:
                add(f"packages/{package.name}", root, (root / relative).resolve(), relative)
            build = root / ".lake" / "build"
            add_build(f"packages/{package.name}/.lake/build", build)
        return {
            "schema_version": 1,
            "identity_kind": "release-artifacts",
            "files": sorted(records, key=lambda value: value["path"]),
            "digest": bundle.canonical_digest("fixture-artifacts", records),
        }

    @staticmethod
    def compute_validator_tool_identity(root: Path) -> dict[str, object]:
        toolchain = root / ".lake" / "fixture-toolchain"
        runtime = FakeReleaseValidation.compute_toolchain_runtime_identity(toolchain)
        executables = {}
        versions = {
            "lean": "Lean fixture v4.33.1 linux x86_64",
            "lake": "Lake fixture 5",
            "leanchecker": "Lean fixture v4.33.1 linux x86_64",
        }
        for name in ("lean", "lake", "leanchecker"):
            path = (toolchain / "bin" / name).resolve()
            executables[name] = {
                "selected_path": str(path), "sha256": bundle.sha256_file(path),
                "relative_path": f"bin/{name}",
                "version": versions[name],
            }
        return {
            "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
            "selected_toolchain_root": str(toolchain.resolve()),
            **runtime,
            "elan": {"sha256": "sha256:" + "8" * 64, "version": "elan fixture",
                     "invocation_path": "/fixture/elan", "resolved_path": "/fixture/elan"},
            "executables": executables,
        }

    @staticmethod
    def compute_toolchain_runtime_identity(toolchain_root: Path) -> dict[str, object]:
        records = []
        for directory in ("bin", "lib"):
            root = toolchain_root / directory
            for path in bundle._iter_tree(root, exclude=set()):
                records.append({
                    "path": f"toolchain/{directory}/{path.relative_to(root).as_posix()}",
                    "size_bytes": path.stat().st_size,
                    "sha256": bundle.sha256_file(path),
                    "executable": bool(path.stat().st_mode & 0o100),
                })
        records.sort(key=lambda value: value["path"])
        return {
            "runtime_file_count": len(records),
            "runtime_digest": bundle.canonical_digest(
                "CertifiedJL-release-toolchain-runtime-v1", records,
            ),
        }

    @staticmethod
    def validator_tool_portable_projection(record: dict[str, object]) -> dict[str, object]:
        return {
            "lean_toolchain": record["lean_toolchain"],
            "elan": {key: record["elan"][key] for key in ("sha256", "version")},
            "executables": {
                name: {key: record["executables"][name][key]
                       for key in ("relative_path", "sha256", "version")}
                for name in ("lean", "lake", "leanchecker")
            },
            "runtime_file_count": record["runtime_file_count"],
            "runtime_digest": record["runtime_digest"],
        }

    @staticmethod
    def validation_evidence_inventory(receipt: dict[str, object]) -> list[dict[str, object]]:
        records = [dict(step["log"]) for step in receipt["execution"]["steps"]]
        records.extend(dict(receipt["reviewer_workspace"][field])
                       for field in ("review_lean", "theorem_map", "review_olean"))
        records.extend(dict(receipt["all_production_import_root"][field])
                       for field in ("source", "olean"))
        return sorted(records, key=lambda value: value["path"])

    @staticmethod
    def verify_validator_tool_identity(expected: object, root: Path) -> None:
        if expected != FakeReleaseValidation.compute_validator_tool_identity(root):
            raise bundle.BundleError("tool identity mismatch")

    @staticmethod
    def verify_release_receipt(
        path: Path, *, expected_proof_identity: dict[str, object] | None = None,
        evidence_root: Path | None = None, check_live_tools: bool = False,
        tool_root: Path | None = None,
    ) -> dict[str, object]:
        receipt = json.loads(path.read_text(encoding="utf-8"))
        unsigned = {key: value for key, value in receipt.items() if key != "receipt_digest"}
        if receipt.get("success") is not True:
            raise bundle.BundleError("unsuccessful release receipt")
        if receipt.get("receipt_digest") != bundle.canonical_digest("fixture-receipt", unsigned):
            raise bundle.BundleError("bad release receipt digest")
        if expected_proof_identity is not None:
            if expected_proof_identity.get("identity_kind") == "proof-bundle-inputs":
                actual = FakeReleaseValidation.proof_identity_projection(receipt["source_identity"])
            else:
                actual = receipt["source_identity"]
            if actual != expected_proof_identity:
                raise bundle.BundleError("release receipt identity mismatch")
        root = path.parent if evidence_root is None else evidence_root
        for record in FakeReleaseValidation.validation_evidence_inventory(receipt):
            candidate = root / record["path"]
            if (not candidate.is_file() or candidate.stat().st_size != record["size_bytes"]
                    or bundle.sha256_file(candidate) != record["sha256"]):
                raise bundle.BundleError("release evidence differs")
        return receipt

    @staticmethod
    def receipt_semantics(receipt: dict[str, object]) -> tuple[dict[str, object], dict[str, object], str]:
        return receipt["source_identity"], receipt["artifact_identity"], receipt["receipt_digest"]


def write_executable(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    path.chmod(0o755)


def rewrite_tar(source: Path, output: Path, mutate) -> None:
    members: list[tuple[tarfile.TarInfo, bytes]] = []
    with tarfile.open(source, "r") as archive:
        for old in archive.getmembers():
            data = archive.extractfile(old).read()
            info = copy.copy(old)
            members.append((info, data))
    members = mutate(members)
    with tarfile.open(output, "w") as archive:
        for info, data in members:
            info.size = len(data)
            archive.addfile(info, io.BytesIO(data))


class ProofBundleTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / "Main.lean").write_text(
            "/- Authors: Anonymous Author -/\ntheorem tiny : True := by trivial\n"
        )
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        (self.project / "lakefile.toml").write_text(
            'name = "Fixture"\ndefaultTargets = ["Main"]\n', encoding="utf-8",
        )
        self.packages = self.root / "packages"
        self.packages.mkdir()
        self.dependency = self.packages / "dep"
        self.dependency.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=self.dependency, check=True)
        subprocess.run(["git", "config", "user.email", "fixture@example.com"], cwd=self.dependency, check=True)
        subprocess.run(["git", "config", "user.name", "Fixture"], cwd=self.dependency, check=True)
        (self.dependency / "Dep.lean").write_text("def dependencyValue := 1\n")
        dependency_docs = self.dependency / "docs"
        dependency_docs.mkdir()
        (dependency_docs / "README.md").symlink_to("../Dep.lean")
        dep_build = self.dependency / ".lake" / "build" / "lib" / "lean"
        dep_build.mkdir(parents=True)
        (dep_build / "Dep.olean").write_bytes(b"dependency olean")
        (dep_build / "Dep.ilean").write_bytes(b"dependency ilean")
        (self.dependency / ".lake/build/lib/libDep.dylib").write_bytes(b"native runtime")
        (self.dependency / ".lake/build/lib/libDep.so.1").write_bytes(b"versioned native runtime")
        (self.dependency / ".lake/build/lib/libDep.so").symlink_to("libDep.so.1")
        (dep_build / "Dep.trace").write_text("private build path")
        subprocess.run(["git", "add", "Dep.lean", "docs/README.md"], cwd=self.dependency, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=self.dependency, check=True)
        ignored_cache = self.dependency / "widget" / "package-lock.json.hash"
        ignored_cache.parent.mkdir()
        ignored_cache.write_text("untracked private cache\n")
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.dependency, text=True).strip()
        (self.project / "lake-manifest.json").write_text(json.dumps({
            "version": "1.2.0", "packages": [{
                "name": "dep", "type": "git", "url": "https://invalid.example/dep",
                "rev": revision, "scope": "", "subDir": None,
                "manifestFile": "lake-manifest.json", "configFile": "lakefile.toml",
                "inherited": False,
            }],
        }))
        generator = self.project / "scripts" / "reviewer_workspace.py"
        write_executable(generator, """#!/usr/bin/env python3
import argparse, json
from pathlib import Path
p = argparse.ArgumentParser(); p.add_argument('--root', type=Path); p.add_argument('--output', type=Path)
a = p.parse_args(); a.output.mkdir(parents=True)
(a.output / 'Review.lean').write_text('import Main\\n#check tiny\\n')
(a.output / 'theorem-map.json').write_text(json.dumps({'tiny': 'Main.tiny'}, sort_keys=True) + '\\n')
""")
        paper = self.project / "paper"
        paper.mkdir()
        (paper / "paper.tex").write_text("Final paper one\n")
        project_build = self.project / ".lake" / "build" / "lib" / "lean"
        project_build.mkdir(parents=True)
        (project_build / "Main.olean").write_bytes(b"project olean")
        (project_build / "Main.ilean").write_bytes(b"project ilean")
        (self.project / ".lake/build/lib/libMain.dylib").write_bytes(b"native runtime")
        (project_build / "Main.hash").write_text("private build path")
        subprocess.run(["git", "init", "-q"], cwd=self.project, check=True)
        subprocess.run(["git", "config", "user.email", "fixture@example.com"], cwd=self.project, check=True)
        subprocess.run(["git", "config", "user.name", "Fixture"], cwd=self.project, check=True)
        subprocess.run([
            "git", "add", "Main.lean", "lean-toolchain", "lakefile.toml",
            "lake-manifest.json", "scripts/reviewer_workspace.py", "paper/paper.tex",
        ], cwd=self.project, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=self.project, check=True)
        self.tools = self.project / ".lake" / "fixture-toolchain" / "bin"
        self.lean = self.tools / "lean"
        self.lake = self.tools / "lake"
        write_executable(self.lean, "#!/bin/sh\necho 'Lean fixture v4.33.1 linux x86_64'\n")
        write_executable(self.lake, "#!/bin/sh\necho 'Lake fixture 5'\n")
        write_executable(
            self.tools / "leanchecker",
            "#!/bin/sh\necho 'leanchecker has no version command' >&2\nexit 1\n",
        )
        tool_lib = self.project / ".lake" / "fixture-toolchain" / "lib"
        tool_lib.mkdir(parents=True)
        (tool_lib / "liblean-fixture.so").write_bytes(b"fixture runtime")
        generated = self.root / "receipt-review"
        subprocess.run([
            str(generator), "--root", str(self.project), "--output", str(generated),
        ], check=True)
        identity = FakeReleaseValidation.compute_release_identity(self.project)
        artifact_identity = FakeReleaseValidation.compute_artifact_identity(
            self.project / ".lake" / "build", self.packages,
        )
        evidence_log = self.root / "logs" / "00-fixture.log"
        evidence_log.parent.mkdir()
        evidence_log.write_text("fixture validation passed\n")
        generated_source = self.root / "CertifiedJLReleaseAll.lean"
        generated_source.write_text("import Main\n")
        generated_olean = self.root / "CertifiedJLReleaseAll.olean"
        generated_olean.write_bytes(b"generated olean")
        def evidence(path: Path) -> dict[str, object]:
            return {
                "path": path.relative_to(self.root).as_posix(),
                "sha256": bundle.sha256_file(path), "size_bytes": path.stat().st_size,
            }
        receipt: dict[str, object] = {
            "schema_version": 1,
            "record_kind": "release-validation-receipt",
            "success": True,
            "source_identity": identity,
            "artifact_identity": artifact_identity,
            "environment": {
                "tools": FakeReleaseValidation.compute_validator_tool_identity(self.project),
            },
            "reviewer_workspace": {
                "review_lean": evidence(generated / bundle.REVIEW_NAME),
                "theorem_map": evidence(generated / bundle.THEOREM_MAP_NAME),
                "review_olean": evidence(generated_olean),
            },
            "all_production_import_root": {
                "source": evidence(generated_source), "olean": evidence(generated_olean),
            },
            "execution": {"steps": [{"log": evidence(evidence_log)}]},
        }
        receipt["receipt_digest"] = bundle.canonical_digest("fixture-receipt", receipt)
        self.receipt = self.root / "release-receipt.json"
        self.receipt.write_text(json.dumps(receipt), encoding="utf-8")
        self.fake_patch = mock.patch.object(
            bundle, "_load_release_validation", return_value=FakeReleaseValidation,
        )
        self.fake_patch.start()

    def tearDown(self) -> None:
        self.fake_patch.stop()
        self.temporary.cleanup()

    def build(self, name: str = "proof.tar") -> tuple[Path, dict[str, object]]:
        output = self.root / name
        manifest = bundle.build_proof_bundle(
            project_root=self.project,
            project_build=self.project / ".lake" / "build",
            packages_root=self.packages,
            receipt_path=self.receipt,
            output=output,
        )
        return output, manifest

    def reseal_source_identity(self) -> None:
        receipt = json.loads(self.receipt.read_text())
        receipt["source_identity"] = FakeReleaseValidation.compute_release_identity(self.project)
        receipt["receipt_digest"] = bundle.canonical_digest(
            "fixture-receipt", {key: value for key, value in receipt.items() if key != "receipt_digest"},
        )
        self.receipt.write_text(json.dumps(receipt), encoding="utf-8")

    def alignment_review(self, proof_manifest: dict[str, object], name: str) -> Path:
        records = bundle._paper_inventory(self.project / "paper")
        review: dict[str, object] = {
            "schema_version": 1,
            "record_kind": "certifiedjl-manuscript-proof-alignment-review",
            "attests_human_review": True,
            "reviewer": (
                proof_manifest["review_guidance"]["review_role"]
                if proof_manifest.get("anonymous_source")
                else "Synthetic fixture reviewer"
            ),
            "reviewed_utc": "2026-09-15T12:00:00Z",
            "paper_tree_digest": bundle.canonical_digest("CertifiedJL-final-paper-tree-v1", records),
            "proof_bundle_id": proof_manifest["bundle_id"],
            "theorem_map_sha256": proof_manifest["reviewer_workspace"]["theorem_map_sha256"],
        }
        review["review_digest"] = bundle.alignment_review_digest(review)
        path = self.root / name
        path.write_text(json.dumps(review), encoding="utf-8")
        return path

    def test_tiny_fixture_build_verify_and_clean_extract_end_to_end(self) -> None:
        archive, manifest = self.build()
        extracted = self.root / "extracted"
        verified = bundle.verify_proof_bundle(archive, extract_to=extracted)
        self.assertEqual(manifest["bundle_id"], verified["bundle_id"])
        self.assertFalse(manifest["anonymous_source"])
        self.assertFalse(manifest["review_guidance"]["records_human_approval"])
        # Host checking executes the same version probes used by validation;
        # leanchecker deliberately has no independent --version interface.
        bundle.verify_proof_bundle(archive, check_host=True)
        self.assertEqual((extracted / "Review.lean").read_text(), "import Main\n#check tiny\n")
        self.assertEqual(
            (extracted / "source/.lake/release-reviewer-workspace/Review.lean").read_bytes(),
            (extracted / "Review.lean").read_bytes(),
        )
        editor = json.loads((extracted / "review.code-workspace").read_text())
        self.assertEqual(editor["folders"], [{"path": "source"}])
        self.assertEqual(
            editor["settings"]["lean4.envPathExtensions"],
            ["../review-bin", "../toolchain/bin"],
        )
        self.assertFalse(editor["settings"]["lean4.automaticallyBuildDependencies"])
        self.assertTrue((extracted / "source/.lake/build/lib/lean/Main.olean").is_file())
        self.assertTrue((extracted / "source/.lake/packages/dep/Dep.lean").is_file())
        materialized_link = extracted / "source/.lake/packages/dep/docs/README.md"
        self.assertTrue(materialized_link.is_file())
        self.assertFalse(materialized_link.is_symlink())
        self.assertEqual(materialized_link.read_text(), "def dependencyValue := 1\n")
        self.assertTrue((extracted / "source/.lake/packages/dep/.lake/build/lib/lean/Dep.ilean").is_file())
        self.assertTrue((extracted / "source/.lake/packages/dep/.lake/build/lib/libDep.dylib").is_file())
        materialized_native_link = (
            extracted / "source/.lake/packages/dep/.lake/build/lib/libDep.so"
        )
        self.assertTrue(materialized_native_link.is_file())
        self.assertFalse(materialized_native_link.is_symlink())
        self.assertEqual(materialized_native_link.read_bytes(), b"versioned native runtime")
        self.assertFalse((extracted / "source/.lake/packages/dep/.lake/build/lib/lean/Dep.trace").exists())
        self.assertTrue((extracted / "source/.lake/build/lib/libMain.dylib").is_file())
        self.assertFalse((extracted / "source/.lake/build/lib/lean/Main.hash").exists())
        self.assertFalse(any(path.is_symlink() for path in extracted.rglob("*")))
        self.assertFalse((extracted / "source/.lake/packages/dep/.git").exists())
        self.assertFalse((extracted / "source/.lake/packages/dep/widget/package-lock.json.hash").exists())
        self.assertEqual(manifest["platform"]["system"], bundle.platform.system())
        self.assertEqual(manifest["toolchain"]["lean_toolchain"], "leanprover/lean4:v4.33.1")
        self.assertTrue((extracted / "toolchain/bin/lean").is_file())
        overrides = json.loads(
            (extracted / "source/.lake/release-package-overrides.json").read_text()
        )
        self.assertEqual(overrides["packages"][0]["type"], "path")
        self.assertEqual(overrides["packages"][0]["dir"], ".lake/packages/dep")
        wrapper = extracted / "review-bin/lake"
        self.assertTrue(wrapper.stat().st_mode & stat.S_IXUSR)
        wrapper_version = subprocess.check_output(
            [str(wrapper), "--version"], text=True,
        ).strip()
        self.assertEqual(wrapper_version, "Lake fixture 5")
        self.assertEqual(manifest["toolchain"]["runtime_file_count"], 4)
        with self.assertRaisesRegex(bundle.BundleError, "must be new"):
            bundle.verify_proof_bundle(archive, extract_to=extracted)

    def test_receipt_failure_and_unbound_generated_file_fail_closed(self) -> None:
        receipt = json.loads(self.receipt.read_text())
        receipt["success"] = False
        receipt["receipt_digest"] = bundle.canonical_digest(
            "fixture-receipt", {k: v for k, v in receipt.items() if k != "receipt_digest"},
        )
        self.receipt.write_text(json.dumps(receipt))
        with self.assertRaisesRegex(bundle.BundleError, "unsuccessful"):
            self.build()
        receipt["success"] = True
        receipt["reviewer_workspace"]["review_lean"]["sha256"] = "sha256:" + "0" * 64
        receipt["receipt_digest"] = bundle.canonical_digest(
            "fixture-receipt", {k: v for k, v in receipt.items() if k != "receipt_digest"},
        )
        self.receipt.write_text(json.dumps(receipt))
        with self.assertRaisesRegex(bundle.BundleError, "release evidence differs|does not bind"):
            self.build()

    def test_missing_dependency_artifacts_are_rejected(self) -> None:
        (self.dependency / ".lake/build/lib/lean/Dep.olean").unlink()
        with self.assertRaisesRegex(bundle.BundleError, "no compiled .olean"):
            self.build()

    def test_tracked_dependency_symlink_escape_is_rejected(self) -> None:
        dependency = self.root / "escaping-dependency"
        dependency.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=dependency, check=True)
        (dependency / "escape").symlink_to(self.root / "release-receipt.json")
        (dependency / ".lake/build").mkdir(parents=True)
        (dependency / ".lake/build/Dep.olean").write_bytes(b"olean")
        subprocess.run(["git", "add", "escape"], cwd=dependency, check=True)
        with self.assertRaisesRegex(bundle.BundleError, "symlink escapes"):
            bundle._copy_dependency_tree(
                dependency, self.root / "escaped-copy", FakeReleaseValidation,
            )

    def test_post_validation_artifact_substitution_and_missing_log_are_rejected(self) -> None:
        project_olean = self.project / ".lake/build/lib/lean/Main.olean"
        project_olean.write_bytes(b"substituted after validation")
        with self.assertRaisesRegex(bundle.BundleError, "validated artifacts"):
            self.build()
        project_olean.write_bytes(b"project olean")
        (self.root / "logs/00-fixture.log").unlink()
        with self.assertRaisesRegex(bundle.BundleError, "release evidence differs|missing release evidence"):
            self.build()

    def test_tamper_missing_and_unexpected_members_are_rejected(self) -> None:
        archive, _manifest = self.build()
        cases = {
            "tampered.tar": lambda records: [
                (info, b"tampered" if info.name.endswith("Main.olean") else data)
                for info, data in records
            ],
            "missing.tar": lambda records: [
                (info, data) for info, data in records if not info.name.endswith("Main.ilean")
            ],
            "unexpected.tar": lambda records: records + [
                (tarfile.TarInfo("unexpected.txt"), b"unexpected")
            ],
        }
        for name, mutation in cases.items():
            with self.subTest(name=name):
                damaged = self.root / name
                rewrite_tar(archive, damaged, mutation)
                with self.assertRaises(bundle.BundleError):
                    bundle.verify_proof_bundle(damaged)

    def test_archive_hash_verification_streams_large_members(self) -> None:
        staging = self.root / "streaming"
        staging.mkdir()
        payload = staging / "large.bin"
        with payload.open("wb") as stream:
            stream.truncate(32 * 1024 * 1024)
        record = {
            "path": "large.bin", "sha256": bundle.sha256_file(payload),
            "size": payload.stat().st_size, "mode": 0o644, "role": "fixture",
        }
        manifest = {"files": [record]}
        (staging / "manifest.json").write_text(json.dumps(manifest))
        archive = self.root / "streaming.tar"
        bundle._write_deterministic_tar(staging, archive, "manifest.json")
        tracemalloc.start()
        parsed, captured, names = bundle._verified_archive(archive, "manifest.json")
        _current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        self.assertEqual(parsed, manifest)
        self.assertEqual(set(captured), {"manifest.json"})
        self.assertIn("large.bin", names)
        self.assertLess(peak, 8 * 1024 * 1024)

    def test_duplicate_traversal_and_link_members_are_rejected(self) -> None:
        archive, _manifest = self.build()
        def duplicate(records):
            return records + [(copy.copy(records[-1][0]), records[-1][1])]
        def traversal(records):
            info = tarfile.TarInfo("../escape")
            return records + [(info, b"escape")]
        for name, mutation in (("duplicate.tar", duplicate), ("traversal.tar", traversal)):
            damaged = self.root / name
            rewrite_tar(archive, damaged, mutation)
            with self.subTest(name=name), self.assertRaises(bundle.BundleError):
                bundle.verify_proof_bundle(damaged)
        linked = self.root / "link.tar"
        with tarfile.open(archive, "r") as original, tarfile.open(linked, "w") as output:
            for member in original.getmembers():
                output.addfile(copy.copy(member), io.BytesIO(original.extractfile(member).read()))
            info = tarfile.TarInfo("link")
            info.type = tarfile.SYMTYPE
            info.linkname = "Review.lean"
            output.addfile(info)
        with self.assertRaisesRegex(bundle.BundleError, "link, directory, or special"):
            bundle.verify_proof_bundle(linked)

    def test_submission_separates_paper_and_frozen_proof_identity(self) -> None:
        archive, proof_manifest = self.build()
        first = self.root / "submission-one.tar"
        first_review = self.alignment_review(proof_manifest, "first-review.json")
        first_manifest = bundle.compose_submission(
            project_root=self.project, paper_root=self.project / "paper",
            proof_bundle=archive, alignment_review=first_review, output=first,
        )
        (self.project / "paper/paper.tex").write_text("Final paper two\n")
        second = self.root / "submission-two.tar"
        second_review = self.alignment_review(proof_manifest, "second-review.json")
        second_manifest = bundle.compose_submission(
            project_root=self.project, paper_root=self.project / "paper",
            proof_bundle=archive, alignment_review=second_review, output=second,
        )
        self.assertEqual(
            first_manifest["proof_bundle"]["bundle_id"], proof_manifest["bundle_id"],
        )
        self.assertEqual(
            second_manifest["proof_bundle"]["bundle_id"], proof_manifest["bundle_id"],
        )
        self.assertNotEqual(first_manifest["paper"]["tree_digest"], second_manifest["paper"]["tree_digest"])
        bundle.verify_submission(second)
        (self.project / "Main.lean").write_text("theorem tiny : False := by trivial\n")
        with self.assertRaisesRegex(bundle.BundleError, "proof inputs differ"):
            bundle.compose_submission(
                project_root=self.project, paper_root=self.project / "paper",
                proof_bundle=archive, alignment_review=second_review,
                output=self.root / "bad-submission.tar",
            )

    def test_anonymous_profile_projects_identified_checkout_and_fails_closed(self) -> None:
        identified_main = (self.project / "Main.lean").read_text()
        anonymous_main = identified_main.replace("Anonymous Author", "Anonymous Author")
        marker = self.project / bundle.ANONYMOUS_SOURCE_MARKER
        marker.write_text(json.dumps(bundle.ANONYMOUS_SOURCE_PROFILE), encoding="utf-8")
        (self.project / "Main.lean").write_text(anonymous_main)
        subprocess.run(["git", "add", "Main.lean", marker.name], cwd=self.project, check=True)
        subprocess.run(["git", "commit", "-qm", "anonymous fixture"], cwd=self.project, check=True)
        self.reseal_source_identity()
        proof, proof_manifest = self.build("anonymous-proof.tar")
        self.assertTrue(proof_manifest["anonymous_source"])
        self.assertEqual(
            proof_manifest["review_guidance"]["review_role"],
            "independent-anonymous-artifact-reviewer",
        )
        self.assertFalse(proof_manifest["review_guidance"]["records_human_approval"])
        pointer_path = self.root / "anonymous-freeze.json"
        pointer = bundle.write_freeze_pointer(proof, pointer_path)
        self.assertTrue(pointer["anonymous_source"])

        (self.project / "Main.lean").write_text(identified_main)
        marker.unlink()
        subprocess.run(["git", "add", "-A"], cwd=self.project, check=True)
        subprocess.run(["git", "commit", "-qm", "identified fixture"], cwd=self.project, check=True)

        @contextmanager
        def projected_source(root: Path):
            with tempfile.TemporaryDirectory() as directory:
                projected = Path(directory) / "source"
                shutil.copytree(root, projected, ignore=shutil.ignore_patterns(".git"))
                (projected / "Main.lean").write_text(
                    (projected / "Main.lean").read_text().replace(
                        "Anonymous Author", "Anonymous Author",
                    )
                )
                (projected / bundle.ANONYMOUS_SOURCE_MARKER).write_text(
                    json.dumps(bundle.ANONYMOUS_SOURCE_PROFILE), encoding="utf-8",
                )
                yield projected

        private_helper = types.SimpleNamespace(projected_source=projected_source)
        with mock.patch.object(bundle.importlib, "import_module", return_value=private_helper):
            (self.project / "paper/paper.tex").write_text("anonymous paper-only edit\n")
            bundle.check_freeze(self.project, pointer_path)
            review = self.alignment_review(proof_manifest, "anonymous-review.json")
            submission = self.root / "anonymous-submission.tar"
            submission_manifest = bundle.compose_submission(
                project_root=self.project, paper_root=self.project / "paper",
                proof_bundle=proof, alignment_review=review, output=submission,
            )
            self.assertTrue(submission_manifest["proof_bundle"]["anonymous_source"])
            identifying_review = json.loads(review.read_text())
            identifying_review["reviewer"] = "Identifying Reviewer Name"
            identifying_review["review_digest"] = bundle.alignment_review_digest(
                identifying_review
            )
            identifying_path = self.root / "identifying-anonymous-review.json"
            identifying_path.write_text(json.dumps(identifying_review), encoding="utf-8")
            with self.assertRaisesRegex(bundle.BundleError, "fixed public reviewer role"):
                bundle.compose_submission(
                    project_root=self.project, paper_root=self.project / "paper",
                    proof_bundle=proof, alignment_review=identifying_path,
                    output=self.root / "identifying-anonymous-submission.tar",
                )

            (self.project / "Main.lean").write_text(
                identified_main.replace("True", "False")
            )
            with self.assertRaisesRegex(bundle.BundleError, "proof inputs differ"):
                bundle.check_freeze(self.project, pointer_path)
            (self.project / "Main.lean").write_text(identified_main)
            generator = self.project / "scripts/reviewer_workspace.py"
            generator.write_text(generator.read_text() + "\n# procedure changed\n")
            with self.assertRaisesRegex(bundle.BundleError, "validation procedure changed"):
                bundle.compose_submission(
                    project_root=self.project, paper_root=self.project / "paper",
                    proof_bundle=proof, alignment_review=review,
                    output=self.root / "anonymous-stale-procedure.tar",
                )

        def change_profile(records):
            changed = []
            for info, data in records:
                if info.name == bundle.MANIFEST_NAME:
                    document = json.loads(data)
                    document["anonymous_source"] = False
                    document["review_guidance"] = bundle._review_guidance(False)
                    document["bundle_id"] = bundle._manifest_digest(document)
                    data = bundle._json_bytes(document)
                changed.append((info, data))
            return changed

        profile_tamper = self.root / "anonymous-profile-tamper.tar"
        rewrite_tar(proof, profile_tamper, change_profile)
        with self.assertRaisesRegex(bundle.BundleError, "anonymity profile"):
            bundle.verify_proof_bundle(profile_tamper)

    def test_invalid_anonymous_marker_is_rejected(self) -> None:
        marker = self.project / bundle.ANONYMOUS_SOURCE_MARKER
        marker.write_text('{"record_kind":"anonymous-source"}\n')
        with self.assertRaisesRegex(bundle.BundleError, "unexpected profile"):
            self.build("invalid-anonymous-marker.tar")

    def test_procedure_change_requires_revalidation_but_freeze_guard_stays_proof_only(self) -> None:
        archive, proof_manifest = self.build()
        pointer_path = self.root / "freeze.json"
        pointer = bundle.write_freeze_pointer(archive, pointer_path)
        self.assertEqual(pointer["bundle_id"], proof_manifest["bundle_id"])
        (self.project / "paper/paper.tex").write_text("paper-only edit\n")
        bundle.check_freeze(self.project, pointer_path)
        generator = self.project / "scripts/reviewer_workspace.py"
        generator.write_text(generator.read_text() + "\n# validation procedure changed\n")
        bundle.check_freeze(self.project, pointer_path)
        review = self.alignment_review(proof_manifest, "procedure-review.json")
        with self.assertRaisesRegex(bundle.BundleError, "validation procedure changed"):
            bundle.compose_submission(
                project_root=self.project, paper_root=self.project / "paper",
                proof_bundle=archive, alignment_review=review,
                output=self.root / "procedure-stale.tar",
            )
        pointer = json.loads(pointer_path.read_text())
        pointer["proof_identity"]["proof_closure_digest"] = "sha256:" + "0" * 64
        pointer_path.write_text(json.dumps(pointer))
        with self.assertRaisesRegex(bundle.BundleError, "invalid proof freeze pointer"):
            bundle.check_freeze(self.project, pointer_path)

    def test_submission_requires_exact_human_alignment_record(self) -> None:
        proof, proof_manifest = self.build()
        review = self.alignment_review(proof_manifest, "invalid-review.json")
        record = json.loads(review.read_text())
        record["attests_human_review"] = False
        record["review_digest"] = bundle.alignment_review_digest(record)
        review.write_text(json.dumps(record))
        with self.assertRaisesRegex(bundle.BundleError, "human-review record"):
            bundle.compose_submission(
                project_root=self.project, paper_root=self.project / "paper",
                proof_bundle=proof, alignment_review=review,
                output=self.root / "unreviewed.tar",
            )

    def test_submission_nested_bundle_and_paper_tamper_are_rejected(self) -> None:
        proof, proof_manifest = self.build()
        submission = self.root / "submission.tar"
        review = self.alignment_review(proof_manifest, "review.json")
        bundle.compose_submission(
            project_root=self.project, paper_root=self.project / "paper",
            proof_bundle=proof, alignment_review=review, output=submission,
        )
        for name, suffix in (("proof-tamper.tar", bundle.PROOF_ARCHIVE_NAME),
                             ("paper-tamper.tar", "paper/paper.tex")):
            damaged = self.root / name
            rewrite_tar(submission, damaged, lambda records, suffix=suffix: [
                (info, data + b"x" if info.name == suffix else data) for info, data in records
            ])
            with self.subTest(name=name), self.assertRaises(bundle.BundleError):
                bundle.verify_submission(damaged)


if __name__ == "__main__":
    unittest.main()
