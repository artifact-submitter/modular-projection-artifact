#!/usr/bin/env python3

from copy import deepcopy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import submission_alignment as alignment
from proof_bundle import BundleError, _validate_alignment_review


class AlignmentTests(unittest.TestCase):
    def test_prepare_does_not_attest_review_and_record_requires_current_inputs(self):
        manifest = {
            "bundle_id": "sha256:" + "1" * 64,
            "reviewer_workspace": {"theorem_map_sha256": "sha256:" + "2" * 64},
        }
        with tempfile.TemporaryDirectory() as directory, patch.object(
            alignment, "verify_proof_bundle", return_value=manifest,
        ):
            root = Path(directory)
            (root / "paper.tex").write_text("A claim.")
            pending = alignment.prepare(root, root / "unused.tar")
            self.assertFalse(pending["attests_human_review"])
            with self.assertRaises(BundleError):
                _validate_alignment_review(
                    pending, paper_digest=pending["paper_tree_digest"], proof_manifest=manifest,
                )
            review = alignment.record_review(pending, pending, "Test fixture reviewer")
            self.assertEqual(_validate_alignment_review(
                review, paper_digest=pending["paper_tree_digest"], proof_manifest=manifest,
            ), review)
            with self.assertRaises(BundleError):
                alignment.record_review(pending, pending, " ")
            changed = deepcopy(pending)
            changed["paper_tree_digest"] = "sha256:" + "3" * 64
            with self.assertRaises(BundleError):
                alignment.record_review(pending, changed, "Test fixture reviewer")
            (root / "paper.tex").write_text("A changed claim.")
            self.assertNotEqual(alignment.prepare(root, root / "unused.tar"), pending)

    def test_cli_requires_explicit_attestation(self):
        with self.assertRaises(SystemExit) as stopped:
            alignment.main([
                "record-review", "--paper-root", ".", "--proof-bundle", "p.tar",
                "--pending", "pending.json", "--reviewer", "Test fixture reviewer",
                "--output", "review.json",
            ])
        self.assertEqual(stopped.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
