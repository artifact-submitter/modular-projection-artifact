#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

import validation_roots


EXPECTED_FAST_ROOTS = {
    "CertifiedJL.Tests.StatementCanaries",
    "CertifiedJL.Tests.ModelCanaries",
    "CertifiedJL.Tests.ObstructionCanariesFast",
    "CertifiedJL.Tests.RowTensorization",
    "CertifiedJL.Tests.SingletonGaussian",
    "CertifiedJL.Tests.AffineL2General",
    "CertifiedJL.Tests.AffineEndpoints",
    "CertifiedJL.Tests.AffineTransports",
    "CertifiedJL.Tests.RowTransports",
    "CertifiedJL.Tests.GaussianKernelIdentities",
    "CertifiedJL.Tests.TernaryLInfTwoDecimalThreshold",
    "CertifiedJL.Tests.SparseOneRowProfileSplitImport",
    "CertifiedJL.Tests.CertificateReplayAlternatives",
    "CertifiedJLFast",
    "CertifiedJLFast.Tests.AxiomFootprints",
    "CertifiedJLFast.Tests.PublicAPI",
}

EXPECTED_KERNEL_CANARIES = {
    "CertifiedJL.Tests.AxiomFootprints",
    "CertifiedJL.Tests.AffineResultAxioms",
    "CertifiedJL.Tests.StatementCanaries",
    "CertifiedJL.Tests.ModelCanaries",
    "CertifiedJL.Tests.PublicAPI",
    "CertifiedJL.Tests.ObstructionCanaries",
    "CertifiedJL.Tests.LiteratureCounterexamples",
    "CertifiedJL.Tests.MainTheoremNotation",
    "CertifiedJL.Tests.TernaryLInfTwoDecimalThreshold",
    "CertifiedJL.Tests.TernaryLInfTwoDecimalFourierBridge",
    "CertifiedJL.Tests.ClosedIntervalTransfer",
    "CertifiedJL.Tests.RowTensorization",
    "CertifiedJL.Tests.SingletonGaussian",
    "CertifiedJL.Tests.AffineL2General",
    "CertifiedJL.Tests.AffineEndpoints",
    "CertifiedJL.Tests.AffineTransports",
    "CertifiedJL.Tests.RowTransports",
    "CertifiedJL.Tests.GaussianKernelIdentities",
    "CertifiedJL.Tests.EndpointRiemann",
    "CertifiedJL.Tests.FiniteConditioningLower",
    "CertifiedJL.Tests.SeedPartition",
    "CertifiedJL.Tests.OneRowCertificateCanaries",
    "CertifiedJL.Tests.OneRowReplayCanaries",
    "CertifiedJL.Tests.UpperTailCanaries",
}

EXPECTED_SPARSE_LOWER_FAMILIES = {
    "ternary-threshold-lower",
    "ternary-threshold-lower-192-bits128",
    "ternary-threshold-lower-256-bits192",
    "ternary-threshold-lower-384-bits192",
    "ternary-threshold-lower-512-bits192",
    "ternary-threshold-lower-512-floor73-bits193",
    "ternary-threshold-lower-512-bits256",
}


class ValidationRootsTests(unittest.TestCase):
    def test_repository_plan_preserves_every_validation_root(self) -> None:
        plan = validation_roots.load_plan()
        self.assertEqual(set(plan["fast"]["targets"]), EXPECTED_FAST_ROOTS)
        self.assertEqual(
            set(plan["kernel-canaries"]["targets"]), EXPECTED_KERNEL_CANARIES
        )
        self.assertEqual(
            set(plan["sparse-lower"]["family_ids"]),
            EXPECTED_SPARSE_LOWER_FAMILIES,
        )
        self.assertEqual(len(plan["sparse-lower"]["targets"]), 35)

    def test_environment_override_controls_batch_size(self) -> None:
        self.assertEqual(validation_roots.batch_size("sparse-lower", environ={}), 1)
        self.assertEqual(
            validation_roots.batch_size(
                "sparse-lower", environ={"CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE": "3"}
            ),
            3,
        )

    def test_invalid_environment_override_is_rejected(self) -> None:
        with self.assertRaisesRegex(SystemExit, "must be a positive integer"):
            validation_roots.batch_size(
                "sparse-lower", environ={"CERTIFIEDJL_SPARSE_LOWER_BATCH_SIZE": "0"}
            )

    def test_duplicate_root_is_rejected(self) -> None:
        source = validation_roots.PLAN.read_text()
        changed = source.replace(
            '  "CertifiedJL.Tests.StatementCanaries",',
            '  "CertifiedJL.Tests.StatementCanaries",\n'
            '  "CertifiedJL.Tests.StatementCanaries",',
            1,
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "validation-roots.toml"
            path.write_text(changed)
            with self.assertRaisesRegex(SystemExit, "duplicate Lean root"):
                validation_roots.load_plan(path)

    def test_unknown_replay_family_is_rejected(self) -> None:
        source = validation_roots.PLAN.read_text()
        changed = source.replace(
            '  "ternary-threshold-lower-512-bits256",',
            '  "ternary-threshold-lower-does-not-exist",',
            1,
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "validation-roots.toml"
            path.write_text(changed)
            with self.assertRaisesRegex(SystemExit, "unknown replay family"):
                validation_roots.load_plan(path)


if __name__ == "__main__":
    unittest.main()
