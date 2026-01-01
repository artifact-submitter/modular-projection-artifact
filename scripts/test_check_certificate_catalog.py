#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_certificate_catalog


class CertificateCatalogReproductionTests(unittest.TestCase):
    def test_missing_repository_generator_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory, patch.object(
            check_certificate_catalog, "ROOT", Path(directory)
        ):
            entry = {
                "id": "fixture",
                "generator": "scripts/missing.py",
                "regenerate": "python3 scripts/missing.py --check",
            }
            with self.assertRaisesRegex(SystemExit, "missing generator"):
                check_certificate_catalog.validate_reproduction_metadata(entry)

    def test_missing_regeneration_input_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory, patch.object(
            check_certificate_catalog, "ROOT", Path(directory)
        ):
            entry = {
                "id": "fixture",
                "generator": "hand-authored exact Lean certificate",
                "regenerate": "lake build CertifiedJL/Missing.lean",
            }
            with self.assertRaisesRegex(SystemExit, "regenerate input does not exist"):
                check_certificate_catalog.validate_reproduction_metadata(entry)


if __name__ == "__main__":
    unittest.main()
