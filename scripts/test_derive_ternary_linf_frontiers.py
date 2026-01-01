#!/usr/bin/env python3
"""Mutation tests for the frozen two-decimal ternary L-infinity artifact."""

from __future__ import annotations

from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "derive_ternary_linf_frontiers.py"
SPEC = importlib.util.spec_from_file_location("derive_ternary_linf_frontiers", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class FrozenArtifactMutationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = json.loads(MODULE.DEFAULT_ARTIFACT.read_text())

    def assert_rejected(self, mutate) -> None:
        candidate = deepcopy(self.data)
        mutate(candidate)
        with self.assertRaises(AssertionError):
            MODULE.verify_record(candidate)

    def test_rejects_top_level_analytic_constant_mutation(self) -> None:
        self.assert_rejected(lambda data: data.__setitem__("phi1", "999"))

    def test_rejects_majorant_degree_mutation(self) -> None:
        self.assert_rejected(
            lambda data: data["cases"][1].__setitem__("degree", 1)
        )

    def test_rejects_rows_and_bits_mutation(self) -> None:
        self.assert_rejected(
            lambda data: data["cases"][1].__setitem__("rows_bits", [[1, 999]])
        )

    def test_rejects_tail_metadata_mutation(self) -> None:
        self.assert_rejected(
            lambda data: data["cases"][1].__setitem__("tail_denominator", "1")
        )

    def test_rejects_eighth_moment_tail_threshold_mutation(self) -> None:
        self.assert_rejected(
            lambda data: data["cases"][0].__setitem__("tail_threshold", "8")
        )

    def test_rejects_duplicate_case(self) -> None:
        self.assert_rejected(lambda data: data["cases"].append(data["cases"][2]))

    def test_rejects_duplicate_bernstein_path(self) -> None:
        self.assert_rejected(
            lambda data: data["cases"][1]["central"]["global_paths"].append(
                data["cases"][1]["central"]["global_paths"][0]
            )
        )

    def test_rejects_positive_fourier_tail(self) -> None:
        self.assert_rejected(
            lambda data: data["cases"][1]["diffuse"]["coefficients"].__setitem__(
                3, "1"
            )
        )

    def test_rejects_expectation_objective_mutation(self) -> None:
        self.assert_rejected(
            lambda data: data["cases"][1]["diffuse"].__setitem__(
                "expectation_bound", "1"
            )
        )


if __name__ == "__main__":
    unittest.main()
