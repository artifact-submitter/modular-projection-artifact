#!/usr/bin/env python3
"""Independent enumeration checks for the bounded search arithmetic."""
from collections import Counter
from itertools import product
from fractions import Fraction
import unittest
from search_paper_obstructions import row_counts, squared_sum_counts, linf_search, exceeds


class SearchTests(unittest.TestCase):
    def test_row_by_four_symbol_enumeration(self):
        for vector in ((1,), (1, 2), (1, 1, 1, 1)):
            expected = Counter(sum(a*b for a, b in zip(vector, signs))
                               for signs in product((-1, 0, 0, 1), repeat=len(vector)))
            self.assertEqual(row_counts(vector), expected)

    def test_strict_tail_and_truncation(self):
        row = {0: 2, 1: 1, 4: 1}
        expected = Counter(sum(values) for values in product((0, 0, 1, 4), repeat=3))
        self.assertEqual(squared_sum_counts(row, 3, 4),
                         {x: w for x, w in expected.items() if x <= 4})
        self.assertFalse(exceeds(Fraction(1, 2**128), 128))

    def test_known_closed_equality_witness(self):
        result = linf_search()
        self.assertEqual(result['vectors'], 164)
        half = next(x for x in result['results'] if x['cap'] == '1/2')
        self.assertEqual(half['row_probability'], '91/128')
        self.assertTrue(half['exceeds_128_bits'])


if __name__ == '__main__':
    unittest.main()
