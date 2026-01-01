#!/usr/bin/env python3
"""Keep the bounded geometric experiment tied to the original two cells."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
REPLAY = ROOT / "CertifiedJL/Certificates/Families/L2Lower/Shared/Dominant/Replay"


def cell_payload(source: str, name: str) -> str:
    match = re.search(rf"(?m)^def {name} : (?:Cell|Certificate) where\n((?:  [^\n]+\n)+)", source)
    if match is None:
        raise ValueError(f"missing raw definition: {name}")
    return match.group(1)


class GeometricSampleIdentityTests(unittest.TestCase):
    def test_sample_cells_match_production_inputs(self):
        original = (REPLAY / "ConstantDirectCover128Shard00.lean").read_text()
        sample = (REPLAY / "ConstantDirectCover128GeometricSamples.lean").read_text()
        for name in ("cell0", "certificate0", "cell1", "certificate1"):
            with self.subTest(name=name):
                self.assertEqual(cell_payload(original, name), cell_payload(sample, name))
        self.assertIn("187 / (200 * 2 ^ 128)", original)
        self.assertIn("def budget : ℚ := 187 / (200 * 2 ^ 128)", sample)

    def test_changed_coefficient_is_detected(self):
        sample = (REPLAY / "ConstantDirectCover128GeometricSamples.lean").read_text()
        mutated = sample.replace("24409 / 25000", "24410 / 25000", 1)
        self.assertNotEqual(cell_payload(sample, "certificate0"),
                            cell_payload(mutated, "certificate0"))


if __name__ == "__main__":
    unittest.main()

