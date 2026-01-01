#!/usr/bin/env python3

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from rebuild_frozen_bundle import rebuild_verified_bundle
from release_validation import (
    compute_artifact_identity,
    compute_release_identity,
    compute_toolchain_runtime_identity,
    compute_validator_tool_identity,
    is_release_build_artifact,
    sha256_file,
    write_frozen_package_source_manifest,
    write_frozen_source_manifest,
)


ROOT = Path(__file__).resolve().parent.parent


def write(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


class FrozenBundleRebuildTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)

    def _git_commit(self, root: Path) -> str:
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run([
            "git", "-c", "user.name=Fixture", "-c",
            "user.email=fixture@example.invalid", "commit", "-qm", "fixture",
        ], cwd=root, check=True)
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()

    def _tool_wrapper(self, destination: Path, executable: Path) -> None:
        write(destination, f"#!/bin/sh\nexec {str(executable)!r} \"$@\"\n")
        destination.chmod(0o755)

    def test_true_git_free_dependency_rebuilds_in_new_workspace(self) -> None:
        tools = compute_validator_tool_identity(ROOT)["executables"]
        lake = Path(tools["lake"]["selected_path"])

        dependency = self.base / "dependency"
        dependency.mkdir()
        write(dependency / ".gitignore", ".lake/\n")
        write(dependency / "lean-toolchain", (ROOT / "lean-toolchain").read_text())
        write(dependency / "lakefile.toml", 'name = "Dep"\n[[lean_lib]]\nname = "Dep"\n')
        write(dependency / "lake-manifest.json",
              '{"version":"1.2.0","packages":[],"name":"Dep","lakeDir":".lake"}\n')
        write(dependency / "Dep.lean", "namespace Dep\ntheorem ok : True := trivial\nend Dep\n")
        revision = self._git_commit(dependency)
        subprocess.run([str(lake), "build", "Dep"], cwd=dependency, check=True,
                       stdout=subprocess.DEVNULL)

        source_checkout = self.base / "source-checkout"
        source_checkout.mkdir()
        for relative, value in {
            ".gitignore": ".lake/\n",
            "lean-toolchain": (ROOT / "lean-toolchain").read_text(),
            "lakefile.toml": (
                'name = "FrozenFixture"\n'
                '[[require]]\nname = "dep"\ngit = "https://example.invalid/dep"\n'
                f'rev = "{revision}"\n'
                '[[lean_lib]]\nname = "CertifiedJL"\n'
                '[[lean_lib]]\nname = "CertifiedJLFast"\n'
                '[[lean_lib]]\nname = "Vendor"\n'
            ),
            "CertifiedJL.lean": "import CertifiedJL.Result\n",
            "CertifiedJL/Result.lean": (
                "import Dep\nnamespace Fixture\ntheorem result : True := Dep.ok\nend Fixture\n"
            ),
            "Vendor/V.lean": "namespace Vendor\ntheorem value : True := trivial\nend Vendor\n",
            "CertifiedJLFast.lean": "namespace Fast\ntheorem result : True := trivial\nend Fast\n",
            "CertifiedJL/Tests/Smoke.lean": "import CertifiedJL\nexample : True := Fixture.result\n",
            "scripts/Generate.lean": "def generatedValue : Nat := 1\n",
            "scripts/check_trust.py": "print('trusted')\n",
            "scripts/release_validation.py": (ROOT / "scripts/release_validation.py").read_text(),
            "scripts/native_shadow_replay.py": (ROOT / "scripts/native_shadow_replay.py").read_text(),
            "scripts/lean_source.py": (ROOT / "scripts/lean_source.py").read_text(),
            "scripts/compute_replay_digest.py": (
                ROOT / "scripts/compute_replay_digest.py"
            ).read_text(),
            "scripts/check_replay_families.py": (
                ROOT / "scripts/check_replay_families.py"
            ).read_text(),
            "scripts/reviewer_workspace.py": (ROOT / "scripts/reviewer_workspace.py").read_text(),
            "evidence/result-catalog.toml": (
                '[[result]]\nid = "fixture"\nverification_class = "kernel_checked"\n'
                'lean = "Fixture.result"\nlean_owner = "CertifiedJL/Result.lean"\n'
            ),
            "evidence/theorem-contract.toml": "schema_version = 1\n",
            "evidence/validation-roots.toml": "schema_version = 1\n",
        }.items():
            write(source_checkout / relative, value)
        manifest = {
            "version": "1.2.0", "name": "FrozenFixture", "lakeDir": ".lake",
            "packages": [{
                "url": "https://example.invalid/dep", "type": "git", "subDir": None,
                "scope": "", "rev": revision, "name": "dep",
                "manifestFile": "lake-manifest.json", "inputRev": revision,
                "inherited": False, "configFile": "lakefile.toml",
            }],
        }
        write(source_checkout / "lake-manifest.json", json.dumps(manifest) + "\n")
        self._git_commit(source_checkout)
        identity = compute_release_identity(source_checkout)

        bundle = self.base / "bundle"
        source = bundle / "source"
        tracked = subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=source_checkout,
        ).split(b"\0")
        selected = []
        for raw in tracked:
            if not raw:
                continue
            relative = Path(os.fsdecode(raw))
            destination = source / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_checkout / relative, destination)
            selected.append(destination)
        write_frozen_source_manifest(source, selected, source / "release-source-manifest.json")
        packaged_dependency = source / ".lake/packages/dep"
        for raw in subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=dependency,
        ).split(b"\0"):
            if raw:
                relative = Path(os.fsdecode(raw))
                destination = packaged_dependency / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(dependency / relative, destination)
        for artifact in (dependency / ".lake/build").rglob("*"):
            if artifact.is_file():
                relative = artifact.relative_to(dependency / ".lake/build")
                if is_release_build_artifact(relative):
                    destination = packaged_dependency / ".lake/build" / relative
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(artifact, destination)
        write_frozen_package_source_manifest(
            dependency, packaged_dependency / ".lake/release-package-source-manifest.json"
        )
        self.assertFalse((packaged_dependency / ".git").exists())
        overrides = {"schemaVersion": "1.2.0", "packages": [{
            "type": "path", "scope": "", "name": "dep",
            "manifestFile": "lake-manifest.json", "inherited": False,
            "dir": ".lake/packages/dep", "configFile": "lakefile.toml",
        }]}
        write(source / ".lake/release-package-overrides.json", json.dumps(overrides) + "\n")
        write(source / ".lake/build/POISON", "must not be copied\n")
        empty_build = self.base / "empty-validated-build/lib/lean"
        empty_build.mkdir(parents=True)
        dependency_artifacts = compute_artifact_identity(
            empty_build.parent.parent, source / ".lake/packages"
        )

        for name in ("lean", "lake", "leanchecker"):
            self._tool_wrapper(bundle / "toolchain/bin" / name,
                               Path(tools[name]["selected_path"]))
        (bundle / "toolchain/lib").mkdir(parents=True)
        write(bundle / "review-bin/lake", (
            '#!/bin/sh\nset -eu\nroot=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd -P)\n'
            'exec "$root/toolchain/bin/lake" '
            '--packages="$root/source/.lake/release-package-overrides.json" "$@"\n'
        ))
        (bundle / "review-bin/lake").chmod(0o755)
        write(bundle / "validation-receipt.json", json.dumps({
            "source_identity": identity,
            "artifact_identity": {"package_files": dependency_artifacts["package_files"]},
        }) + "\n")
        runtime = compute_toolchain_runtime_identity(bundle / "toolchain")
        bundle_manifest = {
            "bundle_id": "sha256:" + "1" * 64,
            "proof_identity": {"proof_closure_digest": identity["proof_closure_digest"]},
            "toolchain": runtime,
            "files": [
                {"path": "review-bin/lake", "sha256": sha256_file(bundle / "review-bin/lake")},
                {"path": "source/.lake/release-package-overrides.json",
                 "sha256": sha256_file(source / ".lake/release-package-overrides.json")},
            ],
        }
        workspace = self.base / "workspace"
        output = self.base / "output"
        report = rebuild_verified_bundle(bundle, workspace, output, bundle_manifest)
        self.assertTrue(report["success"])
        self.assertFalse(report["authoritative_release_receipt"])
        self.assertTrue(report["workspace_project_build_initially_absent"])
        self.assertEqual(len(report["steps"]), 10)
        self.assertFalse((workspace / ".lake/build/POISON").exists())
        self.assertTrue((workspace / ".lake/build/lib/lean/CertifiedJL.olean").is_file())
        self.assertTrue((output / "offline-rebuild-report.json").is_file())


if __name__ == "__main__":
    unittest.main()
