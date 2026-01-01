#!/usr/bin/env python3

import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).with_name("generate_sparse_upper_hybrid.py")
SPEC = importlib.util.spec_from_file_location("generate_sparse_upper_hybrid", SCRIPT)
GENERATOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
ORIGINAL_ARGV = sys.argv
try:
    sys.argv = [str(SCRIPT)]
    SPEC.loader.exec_module(GENERATOR)
finally:
    sys.argv = ORIGINAL_ARGV


class SparseUpperHybridTests(unittest.TestCase):
    def test_compact_power_matches_lean_left_association(self):
        experiment = GENERATOR.EXP
        base = experiment.Interval(
            1317439856278233566846238071188431404229388847728505386527370630940419028987491695567073171892024,
            1317439856278233566846238071188431404229388847728505386527370630940419028987491695567073171892028,
        )

        linear = experiment.lean_pow_nat(base, 9)
        binary = base.pow_int(9)

        self.assertEqual(
            linear.hi,
            27592324039149552568572237470400160362769412780754898422658534779214936989874622498715615320510,
        )
        self.assertEqual(binary.hi, linear.hi - 1)

    def test_box13_chunk16_matches_kernel_replay_endpoint(self):
        chunk = GENERATOR.chunk_manifest(13)[16]
        self.assertEqual(chunk[:3], (2, 0, 10))
        self.assertEqual(chunk[3].lo, 0)
        self.assertEqual(
            chunk[3].hi,
            2461353906124008010016579340696586620774364328816230470115467906733377285745878156409334611490,
        )


if __name__ == "__main__":
    unittest.main()
