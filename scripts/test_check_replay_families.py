#!/usr/bin/env python3
"""Mutation tests for the replay-family catalog checker."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "scripts/check_replay_families.py"
SPEC = importlib.util.spec_from_file_location("check_replay_families", CHECKER)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


class ReplayFamilyCatalogTests(unittest.TestCase):
    def test_repository_catalog_is_complete(self) -> None:
        plan = checker.validate()
        self.assertTrue(plan)

    def test_duplicate_assignment_is_rejected(self) -> None:
        source = (ROOT / "evidence/certificates/replay-families.toml").read_text()
        first = checker.validate()[0]
        duplicate = (
            "\n[[family]]\n"
            'id = "duplicate-test"\n'
            f"certificate_ids = [{first['certificate_ids'][0]!r}]\n"
            f"replay_roots = [{first['replay_roots'][0]!r}]\n"
        ).replace("'", '"')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "families.toml"
            path.write_text(source + duplicate)
            with patch.object(checker, "FAMILIES", path):
                with self.assertRaisesRegex(SystemExit, "assigned to both"):
                    checker.validate()

    def test_missing_root_is_rejected(self) -> None:
        source = (ROOT / "evidence/certificates/replay-families.toml").read_text()
        changed = source.replace(
            '"CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs",',
            '"CertifiedJL.Certificates.DoesNotExist",',
            1,
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "families.toml"
            path.write_text(changed)
            with patch.object(checker, "FAMILIES", path):
                with self.assertRaisesRegex(SystemExit, "do not cover"):
                    checker.validate()

    def test_extra_root_is_rejected(self) -> None:
        source = (ROOT / "evidence/certificates/replay-families.toml").read_text()
        changed = source.replace(
            '"CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs",',
            '"CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs",\n'
            '  "CertifiedJL.Certificates.Families.OneRow975.Finite.Soundness",',
            1,
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "families.toml"
            path.write_text(changed)
            with patch.object(checker, "FAMILIES", path):
                with self.assertRaisesRegex(SystemExit, "exceed"):
                    checker.validate()


if __name__ == "__main__":
    unittest.main()
