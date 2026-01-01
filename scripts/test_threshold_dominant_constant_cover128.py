#!/usr/bin/env python3

import importlib.util
from fractions import Fraction
from pathlib import Path
import unittest


SCRIPT = Path(__file__).with_name("threshold_dominant_constant_cover128.py")
SPEC = importlib.util.spec_from_file_location("threshold_dominant_constant_cover128", SCRIPT)
GENERATOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(GENERATOR)


class ThresholdDominantConstantCover128Tests(unittest.TestCase):
    def test_growth_endpoint_is_platform_independent(self):
        r_upper = Fraction(158125, 153664)
        z = Fraction(12, 5)
        exponent = 29 * float(z) * float(r_upper)

        self.assertEqual(exponent.hex(), "0x1.1e7b71204e794p+6")
        self.assertEqual(
            GENERATOR.deterministic_exp(exponent).hex(),
            "0x1.410a4f55cc307p+103",
        )
        self.assertEqual(
            GENERATOR.growth_upper_numerator(r_upper, z),
            12844892618379718333584740712448,
        )


if __name__ == "__main__":
    unittest.main()
