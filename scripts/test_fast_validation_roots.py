#!/usr/bin/env python3

import unittest

from check_fast_import_boundary import fast_replay_failures
from compute_fast_cache_key import closure, leaked_modules
from fast_validation_roots import (
    EXACT_ONLY_ROOTS,
    fast_validation_roots,
)


class FastValidationRootsTest(unittest.TestCase):
    def test_transitive_sample_leaf_is_forbidden_from_fast_roots(self) -> None:
        graph = {
            "Fast.Root": ("Bridge",),
            "Bridge": ("Exact.SampleLeaf",),
            "Exact.SampleLeaf": (),
        }
        self.assertEqual(
            fast_replay_failures(graph, {"Fast.Root"}, {"Exact.SampleLeaf"}),
            [["Fast.Root", "Bridge", "Exact.SampleLeaf"]],
        )

    def test_fast_script_keeps_only_lightweight_obstruction_canaries(self) -> None:
        roots = fast_validation_roots()
        self.assertIn("CertifiedJL.Tests.ObstructionCanariesFast", roots)
        self.assertNotIn("CertifiedJL.Tests.ObstructionCanaries", roots)
        self.assertIn(
            "CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.Verified",
            EXACT_ONLY_ROOTS,
        )

    def test_every_root_participates_in_boundary_and_cache_checks(self) -> None:
        graph = {
            "Fast.Umbrella": ("Safe.Module",),
            "Fast.SecondRoot": ("Bridge",),
            "Bridge": ("Exact.Verified",),
            "Safe.Module": (),
            "Exact.Verified": (),
        }
        roots = {"Fast.Umbrella", "Fast.SecondRoot"}
        forbidden = {"Exact.Verified"}

        self.assertEqual(
            fast_replay_failures(graph, roots, forbidden),
            [["Fast.SecondRoot", "Bridge", "Exact.Verified"]],
        )
        fast_modules = closure(graph, sorted(roots))
        self.assertEqual(leaked_modules(fast_modules, forbidden), ["Exact.Verified"])


if __name__ == "__main__":
    unittest.main()
