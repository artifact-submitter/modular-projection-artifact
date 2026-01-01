#!/usr/bin/env python3
from fractions import Fraction as F
import unittest
from orthus_threshold_rounding import rounded_parameters, compare


class RoundingTests(unittest.TestCase):
    def test_rounded_adapter_is_minimal(self):
        for norm in (F(0), F(1, 10), F(1), F(14, 325), F(1000)):
            for cap, margin in ((F(37, 50), 91), (F(21, 50), 2)):
                result = rounded_parameters(norm, cap, margin)
                b, q = result['public_threshold'], result['minimum_odd_modulus']
                self.assertGreaterEqual(cap*b, F(39, 4)*norm)
                self.assertTrue(b == 1 or cap*(b-1) < F(39, 4)*norm)
                self.assertEqual(q % 2, 1)
                self.assertGreaterEqual(q, margin*b)
                self.assertLess(q-2, margin*b)

    def test_one_and_zero(self):
        self.assertEqual(compare(F(1))['certified_replacement']['public_threshold'], 24)
        self.assertEqual(compare(F(1))['certified_replacement']['minimum_odd_modulus'], 49)
        self.assertEqual(compare(F(0))['certified_replacement']['minimum_odd_modulus'], 3)
        with self.assertRaises(ValueError):
            compare(F(-1))


if __name__ == '__main__':
    unittest.main()
