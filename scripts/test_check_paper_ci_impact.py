#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import subprocess
import tempfile
import unittest

from check_paper_ci_impact import affects_paper, changed_paths, should_run


class PaperImpactTests(unittest.TestCase):
    def test_large_generated_diff_cannot_hide_paper_change(self) -> None:
        paths = [
            f"CertifiedJL/Certificates/Generated/Shard{index:03}.lean"
            for index in range(400)
        ]
        paths.append("paper/sections/certified-jl/abstract.tex")
        self.assertTrue(affects_paper(paths))

    def test_complete_git_diff_finds_paper_change_after_400_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(
                ["git", "config", "user.email", "ci-audit@example.invalid"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "CI Audit"], cwd=root, check=True
            )
            marker = root / "baseline"
            marker.write_text("base\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "base"], cwd=root, check=True)
            base = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=root, text=True
            ).strip()
            generated = root / "CertifiedJL" / "Certificates" / "Generated"
            generated.mkdir(parents=True)
            for index in range(400):
                (generated / f"Shard{index:03}.lean").write_text(
                    f"-- {index}\n", encoding="utf-8"
                )
            paper = root / "paper" / "sections"
            paper.mkdir(parents=True)
            (paper / "late-change.tex").write_text("paper\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "large diff"], cwd=root, check=True)
            head = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=root, text=True
            ).strip()

            paths = changed_paths(base, head, root)
            self.assertIsNotNone(paths)
            self.assertEqual(len(paths), 401)
            self.assertTrue(should_run("pull_request", base, head, root))

    def test_indirect_table_inputs_trigger_paper(self) -> None:
        for path in (
            "evidence/result-catalog.toml",
            "scripts/generate_formalization_table.py",
            ".github/workflows/paper.yml",
            "Makefile",
        ):
            with self.subTest(path=path):
                self.assertTrue(affects_paper([path]))

    def test_unrelated_lean_change_skips_paper(self) -> None:
        self.assertFalse(affects_paper(["CertifiedJL/Model/Row.lean"]))


if __name__ == "__main__":
    unittest.main()
