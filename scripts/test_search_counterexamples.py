#!/usr/bin/env python3
"""Tests for bounded manifest-driven counterexample search."""

from copy import deepcopy
from pathlib import Path
import unittest

from counterexample_probability import ProbabilityError
from check_counterexample_searches import check as check_retained_searches
from search_counterexamples import SearchError, candidates, evaluate_candidate, load_manifest, run_search


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "evidence" / "counterexamples" / "searches" / "q9-margin.toml"


class SearchCounterexamplesTests(unittest.TestCase):
    def setUp(self):
        self.manifest, self.digest = load_manifest(MANIFEST)

    def test_q9_seed_is_exact_and_never_claims_optimality(self):
        result = run_search(self.manifest, self.digest)
        self.assertTrue(result["search_complete"])
        self.assertFalse(result["optimum_claimed"])
        self.assertTrue(result["best_exact_witness"]["refutes_strict_budget"])
        self.assertEqual(result["candidates_examined"], 1)
        self.assertEqual(check_retained_searches(), 1)

    def test_resource_limit_preserves_uncovered_domain(self):
        manifest = deepcopy(self.manifest)
        manifest["max_candidates"] = 1
        manifest["dimensions"] = [16, 17]
        manifest["dimension_max"] = 17
        result = run_search(manifest, self.digest)
        self.assertFalse(result["search_complete"])
        self.assertFalse(result["resource_exhaustion_is_negative_result"])
        self.assertEqual(result["uncovered_domain"]["remaining_candidates"], 1)

    def test_fractional_or_inadmissible_finite_inputs_fail(self):
        for field, value in (("public_threshold", 4.0), ("modulus", 8),
                             ("integer_shifts", [FractionLike()] )):
            manifest = deepcopy(self.manifest)
            manifest[field] = value
            with self.assertRaises((SearchError, ProbabilityError)):
                if field in {"public_threshold", "modulus"}:
                    evaluate_candidate(manifest, [1] * 16, 0)
                else:
                    run_search(manifest, self.digest)
        manifest = deepcopy(self.manifest)
        manifest["minimum_modulus_multiplier_numerator"] = "5"
        manifest["minimum_modulus_multiplier_denominator"] = "2"
        with self.assertRaises(ProbabilityError):
            evaluate_candidate(manifest, [1] * 16, 0)

    def test_negative_coordinate_cap_and_state_limit_fail_closed(self):
        manifest = deepcopy(self.manifest)
        manifest["family"] = "linf-lower"
        manifest["coordinate_cap_numerator"] = "-1"
        manifest["coordinate_cap_denominator"] = "3"
        with self.assertRaises(SearchError):
            evaluate_candidate(manifest, [1] * 16, 0)
        manifest = deepcopy(self.manifest)
        manifest["max_energy_states"] = 1
        result = run_search(manifest, self.digest)
        self.assertFalse(result["search_complete"])
        self.assertEqual(result["uncovered_domain"]["reason"], "time_memory_or_energy_state_limit")

    def test_pre_row_memory_bound_applies_to_both_families(self):
        for family in ("l2-lower", "linf-lower"):
            manifest = deepcopy(self.manifest)
            manifest["family"] = family
            manifest["memory_limit_mb"] = 1
            manifest["dimension_max"] = 4096
            manifest["max_energy_states"] = 10000
            vector = [1] * 4096
            if family == "linf-lower":
                manifest["coordinate_cap_numerator"] = "1"
                manifest["coordinate_cap_denominator"] = "3"
            with self.assertRaises(ProbabilityError):
                evaluate_candidate(manifest, vector, 0)

    def test_large_uncovered_domain_is_compact(self):
        manifest = deepcopy(self.manifest)
        manifest["dimensions"] = [16] * 10000
        manifest["max_candidates"] = 1
        result = run_search(manifest, self.digest)
        self.assertEqual(result["uncovered_domain"]["remaining_candidates"], 9999)
        self.assertNotIn("vectors", result["uncovered_domain"])

    def test_constant_dimension_is_validated_before_allocation(self):
        manifest = deepcopy(self.manifest)
        manifest["dimensions"] = [100000]
        with self.assertRaises(SearchError):
            next(candidates(manifest))

    def test_empty_or_missing_constructor_domains_fail(self):
        for constructor, field in (("constant_vector", "dimensions"),
                                   ("constant_vector", "vector_values"),
                                   ("explicit_vector", "vectors")):
            for mode in ("missing", "empty"):
                manifest = deepcopy(self.manifest)
                manifest["constructor"] = constructor
                if mode == "missing":
                    manifest.pop(field, None)
                else:
                    manifest[field] = []
                with self.assertRaises(SearchError):
                    run_search(manifest, self.digest)

    def test_late_l2_memory_bound_returns_compact_receipt(self):
        manifest = deepcopy(self.manifest)
        manifest["memory_limit_mb"] = 1
        manifest["rows"] = 4096
        result = run_search(manifest, self.digest)
        self.assertFalse(result["search_complete"])
        self.assertEqual(result["uncovered_domain"]["reason"], "time_memory_or_energy_state_limit")


class FractionLike:
    pass


if __name__ == "__main__":
    unittest.main()
