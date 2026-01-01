#!/usr/bin/env python3
"""Negative soundness tests for the external exact artifact."""
from __future__ import annotations

import ast
import hashlib
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "paper/artifact"
ROW = ARTIFACT / "single-row/verify_single_row_975.py"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class ArtifactHardeningTests(unittest.TestCase):
    def test_positive_one_row(self):
        result = subprocess.run([sys.executable, str(ROW)], capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_mutated_target_and_cell_counts(self):
        for old, new in [
            ("TARGET = Fraction(1, 1 << 142)", "TARGET = Fraction(0)"),
            ("CELL_COUNT = 308", "CELL_COUNT = 1"),
            ("CELL_COUNT = 308", "CELL_COUNT = 0"),
        ]:
            with self.subTest(new=new), tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / "mutant.py"
                self.assertIn(old, ROW.read_text())
                path.write_text(ROW.read_text().replace(old, new, 1))
                result = subprocess.run([sys.executable, str(path)], capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn(b"certificate passed", result.stdout)

    def test_gap_overlap_and_missing_endpoint(self):
        row = load("_audit_row", ROW)
        Q = row.Fraction
        for cells in [(), ((Q(0), Q(1, 10)),),
                      ((Q(0), Q(1, 10)), (Q(1, 5), row.DOMAIN_RIGHT)),
                      ((Q(0), Q(1, 5)), (Q(1, 10), row.DOMAIN_RIGHT)),
                      ((Q(0), Q(0)), (Q(0), row.DOMAIN_RIGHT))]:
            with self.subTest(cells=cells), self.assertRaises(ValueError):
                row.verify_cover(cells)

    def test_all_checker_modules_reject_optimization(self):
        for path in sorted(ARTIFACT.rglob("*.py")):
            modes = [(["-O"], None)]
            if path in {ROW, ARTIFACT / "verify_all.py"}:
                modes += [(["-OO"], None), ([], "1")]
            for flags, optimize in modes:
                with self.subTest(path=path.name, flags=flags, optimize=optimize):
                    env = dict(os.environ)
                    env.pop("PYTHONOPTIMIZE", None)
                    if optimize is not None:
                        env["PYTHONOPTIMIZE"] = optimize
                    result = subprocess.run(
                        [sys.executable, *flags, str(path)], env=env,
                        capture_output=True, timeout=60)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(b"requires Python without", result.stderr)

    def test_no_erasable_acceptance_assertions(self):
        for path in ARTIFACT.rglob("*.py"):
            self.assertFalse(any(isinstance(n, ast.Assert)
                                 for n in ast.walk(ast.parse(path.read_text()))),
                             path)

    def test_manifest_rejects_modified_missing_and_unlisted_inputs(self):
        runner = load("_audit_runner", ARTIFACT / "verify_all.py")
        runner.verify_manifest()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(ARTIFACT, root / "paper/artifact",
                            ignore=shutil.ignore_patterns("__pycache__"))
            (root / "evidence").mkdir()
            shutil.copy2(ROOT / "evidence/paper-snapshot.toml", root / "evidence")
            runner.ROOT = root / "paper"
            runner.CHECKERS = tuple(
                runner.replace(c, path=runner.ROOT / c.path.relative_to(ROOT / "paper"))
                for c in runner.CHECKERS)
            runner.verify_manifest()
            target = root / ROW.relative_to(ROOT)
            original = target.read_bytes()
            target.write_bytes(original + b"\n# mutation\n")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                runner.verify_manifest()
            target.unlink()
            with self.assertRaisesRegex(ValueError, "missing"):
                runner.verify_manifest()
            target.write_bytes(original)
            extra = root / "paper/artifact/unpinned-input.txt"
            extra.write_text("unreviewed")
            with self.assertRaisesRegex(ValueError, "unpinned"):
                runner.verify_manifest()

    def test_imported_source_hashes(self):
        import re
        directory = ARTIFACT / "upper-gap"
        for owner, variable, target in [
            ("upper_frontier_contour_core.py", "SPARSE_CORE_SHA256", "verify_U338.py"),
            ("verify_high_security_upper_obstructions.py", "SOURCE_SHA256",
             "verify_upper_frontier_flat_obstructions.py"),
            ("verify_upper_frontier_sparse_contours.py", "CORE_SHA256",
             "upper_frontier_contour_core.py"),
            ("verify_high_security_upper_contour_configs.py", "CORE_SHA256",
             "upper_frontier_contour_core.py"),
        ]:
            expected = re.search(rf'{variable} = "([0-9a-f]{{64}})"',
                                 (directory / owner).read_text()).group(1)
            self.assertEqual(expected, hashlib.sha256((directory / target).read_bytes()).hexdigest())


if __name__ == "__main__":
    unittest.main()
