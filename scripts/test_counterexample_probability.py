#!/usr/bin/env python3
"""Regression tests for exact counterexample arithmetic."""

from collections import Counter
from fractions import Fraction
from itertools import product
import unittest

from counterexample_probability import (
    ProbabilityError,
    centered_residue_counts,
    compare_dyadic_budget,
    convolve_energy_rows,
    coordinate_lower_probability,
    coordinate_upper_probability,
    cutoff_mass,
    identical_energy_convolution,
    integer_shift_residue_counts,
    require_no_wrap,
    squared_energy_distribution,
    validate_modular_instance,
    weighted_row_sums,
)


class ProbabilityTests(unittest.TestCase):
    def test_independent_four_symbol_enumeration(self):
        for vector in ((1,), (1, 2), (1, 1, 1, 1)):
            expected = Counter(sum(a * b for a, b in zip(vector, signs))
                               for signs in product((-1, 0, 0, 1), repeat=len(vector)))
            self.assertEqual(weighted_row_sums(vector), expected)
        with self.assertRaises(ProbabilityError):
            weighted_row_sums([1], {})

    def test_q9_histogram_and_both_convolutions(self):
        row = squared_energy_distribution(
            centered_residue_counts(weighted_row_sums([1] * 16), 9))
        self.assertEqual(row, {0: 607812102, 1: 1154294424, 4: 999371554,
                               9: 823843664, 16: 709645552})
        self.assertEqual(identical_energy_convolution(row, 3, 20),
                         convolve_energy_rows([row, row, row], 20))

    def test_strict_and_closed_cutoffs(self):
        distribution = {0: 1, 1: 2, 2: 4}
        self.assertEqual(cutoff_mass(distribution, 1, "strict_lt"), 1)
        self.assertEqual(cutoff_mass(distribution, 1, "closed_le"), 3)
        self.assertEqual(cutoff_mass(distribution, Fraction(3, 2), "strict_lt"), 3)
        self.assertEqual(cutoff_mass(distribution, 1, "strict_gt"), 4)
        for inexact in (True, 0.5, "1/2"):
            with self.assertRaises(ProbabilityError):
                cutoff_mass(distribution, inexact, "strict_lt")

    def test_equality_refutes_strict_probability_guarantee(self):
        self.assertTrue(compare_dyadic_budget(Fraction(1, 2**128), 128))
        self.assertFalse(compare_dyadic_budget(Fraction(1, 2**128), 128, "closed_le"))

    def test_coordinate_products_include_edge_cases(self):
        for value in (Fraction(0), Fraction(1, 3), Fraction(1)):
            self.assertEqual(coordinate_lower_probability(value, 4), value**4)
            self.assertEqual(coordinate_upper_probability(value, 4), 1 - (1 - value)**4)

    def test_heterogeneous_rows_are_not_replaced_by_a_power(self):
        first, second = {0: 1, 1: 1}, {0: 3, 4: 1}
        self.assertNotEqual(convolve_energy_rows([first, second]),
                            identical_energy_convolution(first, 2))

    def test_integer_shift_and_admissibility(self):
        self.assertEqual(integer_shift_residue_counts({0: 1, 4: 2}, 5, 1), {1: 1, 0: 2})
        validate_modular_instance([2, -2], 1, 5, [0, 1], mask_rows=2,
                                  minimum_modulus_multiplier=Fraction(5, 1))
        for args in (([1], Fraction(1, 2), 5, None), ([3], 1, 5, None), ([1], 1, 4, None),
                     ([1], 1, 5, [Fraction(1, 2)]), ([1], 2, 5, None)):
            with self.assertRaises(ProbabilityError):
                validate_modular_instance(*args)
        with self.assertRaises(ProbabilityError):
            validate_modular_instance([1], 1, 5, [0], mask_rows=2)
        with self.assertRaises(ProbabilityError):
            validate_modular_instance([1], 1, 5, minimum_modulus_multiplier=6)
        with self.assertRaises(ProbabilityError):
            integer_shift_residue_counts({True: 1}, 5, 0)

    def test_no_wrap_requires_sufficient_odd_modulus(self):
        require_no_wrap([1, 2], 7)
        with self.assertRaises(ProbabilityError):
            require_no_wrap([1, 2], 5)
        for vector, modulus in (([], 5), ([1], 4), ([1], 0)):
            with self.assertRaises(ProbabilityError):
                require_no_wrap(vector, modulus)


if __name__ == "__main__":
    unittest.main()
