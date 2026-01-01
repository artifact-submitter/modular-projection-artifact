#!/usr/bin/env python3
"""Mutation tests for the numerical import firewall."""
import unittest
from check_numeric_import_boundary import CORE_ROOTS, NEAR_PREFIX, PREFIX, boundary_failures


class NumericBoundaryTests(unittest.TestCase):
    def test_near_replay_cannot_reimport_analytic_arithmetic(self):
        leaf = NEAR_PREFIX + "Replay.ThresholdNearCoarseShard1111_128"
        partition = NEAR_PREFIX + "Soundness.ThresholdNearCoarsePartition128"
        forbidden = "CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi"
        graph = {root: () for root in CORE_ROOTS}
        graph.update({leaf: (partition,), partition: (forbidden,), forbidden: ()})
        self.assertEqual(boundary_failures(graph), [" -> ".join((leaf, partition, forbidden))])

    def test_transitive_semantic_imports_are_rejected(self):
        leaf = PREFIX + "Replay.ConstantDirectCover128Shard00"
        bridge = PREFIX + "Helper"
        for forbidden in (
            "CertifiedJL.Analysis.Gaussian.GaussianCharacteristic",
            "CertifiedJL.Projection.L2.Lower.BalancedTernary.Lower",
            "CertifiedJL.Probability.Finite.Experiment",
        ):
            with self.subTest(forbidden=forbidden):
                graph = {root: () for root in CORE_ROOTS}
                graph.update({leaf: (bridge,), bridge: (forbidden,), forbidden: ()})
                self.assertEqual(
                    boundary_failures(graph),
                    [" -> ".join((leaf, bridge, forbidden))],
                )

    def test_arithmetic_soundness_imports_are_rejected(self):
        root = PREFIX + "Data.Numeric"
        for forbidden in (
            "CertifiedJL.Arithmetic.Transcendental.Exponential.Exp",
            "CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExp",
            "CertifiedJL.Arithmetic.Transcendental.SquareRoot.Sqrt",
            "CertifiedJL.Arithmetic.Interval.Reflection",
            "CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi",
            "CertifiedJL.Arithmetic.Transcendental.Trigonometric.Trig",
            "CertifiedJL.Arithmetic.Transcendental.Cosh",
            "CertifiedJL.Arithmetic.Transcendental.CubeRoot",
            "CertifiedJL.Arithmetic.Quadrature.FiniteQuadrature",
        ):
            with self.subTest(forbidden=forbidden):
                graph = {root: () for root in CORE_ROOTS}
                graph[root] = (forbidden,)
                self.assertEqual(
                    boundary_failures(graph), [root + " -> " + forbidden]
                )

    def test_numeric_schema_is_allowed_but_missing_core_is_not(self):
        schema = PREFIX + "Data.Cell"
        graph = {root: (schema,) for root in CORE_ROOTS}
        graph[schema] = ()
        self.assertEqual(boundary_failures(graph), [])
        del graph[PREFIX + "Data.Numeric"]
        self.assertEqual(
            boundary_failures(graph),
            ["missing numeric root: " + PREFIX + "Data.Numeric"],
        )

    def test_new_data_module_is_covered_automatically(self):
        graph = {root: () for root in CORE_ROOTS}
        data = PREFIX + "Data.FutureCertificateInput"
        forbidden = "CertifiedJL.Probability.Finite.Experiment"
        graph.update({data: (forbidden,), forbidden: ()})
        self.assertEqual(boundary_failures(graph), [data + " -> " + forbidden])

    def test_data_cannot_import_soundness_or_replay(self):
        data = PREFIX + "Data.FutureCertificateInput"
        for forbidden in (
            PREFIX + "Soundness.NumericSoundness",
            PREFIX + "Replay.ConstantDirectCover128Shard00",
        ):
            with self.subTest(forbidden=forbidden):
                graph = {root: () for root in CORE_ROOTS}
                graph.update({data: (forbidden,), forbidden: ()})
                self.assertEqual(
                    boundary_failures(graph), [data + " -> " + forbidden]
                )

    def test_non_dominant_certificate_data_is_covered(self):
        data = (
            "CertifiedJL.Certificates.Families.L2Upper.ContourFamily."
            "Data.FutureCertificateInput"
        )
        forbidden = (
            "CertifiedJL.Certificates.Families.L2Upper.ContourFamily."
            "Soundness.Soundness"
        )
        graph = {root: () for root in CORE_ROOTS}
        graph.update({data: (forbidden,), forbidden: ()})
        self.assertEqual(boundary_failures(graph), [data + " -> " + forbidden])


if __name__ == "__main__":
    unittest.main()
