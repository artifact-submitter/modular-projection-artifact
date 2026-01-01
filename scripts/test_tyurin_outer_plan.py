#!/usr/bin/env python3
"""Guard the active Tyurin replay route without compiling numerical cells."""

from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "CertifiedJL.Certificates.Families.OneRow975.NormalApproximation"
REPLAY = ROOT / Path(*PREFIX.split(".")) / "Replay/CertificateProofs"


class TyurinOuterPlanTests(unittest.TestCase):
    def test_all_cells_use_scaled_outer_plan(self):
        files = sorted(REPLAY.glob("Cell*.lean"))
        self.assertEqual([f.name for f in files], [f"Cell{i:03d}.lean" for i in range(24)])
        for index, path in enumerate(files):
            text = path.read_text()
            self.assertIn("outerPlanCheck certificateCell = true", text)
            bridge = "closedCore" if index < 20 else "crossingCore"
            self.assertIn(f"cellCertified_of_{bridge}_outerPlan", text)
            self.assertNotIn("outerExactChunkCheck", text)
            self.assertNotIn("certificateData", text)

    def test_superseded_totals_and_generator_are_absent(self):
        family = ROOT / Path(*PREFIX.split("."))
        self.assertFalse((family / "Data/Shard00.lean").exists())
        self.assertFalse((family / "Data/Core.lean").exists())
        self.assertFalse((family / "Soundness/CertificateData.lean").exists())
        self.assertFalse((ROOT / "scripts/GenerateTyurinModerate.lean").exists())
        self.assertFalse((ROOT / "scripts/generate_moderate_certificate_shards.sh").exists())


if __name__ == "__main__":
    unittest.main()
