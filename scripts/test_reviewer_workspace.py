#!/usr/bin/env python3
"""Check reviewer coverage and rejection of malformed catalog references."""

import unittest
from unittest.mock import patch

import reviewer_workspace as review


class ReviewerTests(unittest.TestCase):
    def test_all_catalog_entries_have_statement_and_axiom_commands(self):
        rows = review.entries(review.ROOT)
        text = review.render(rows)
        self.assertGreater(len(rows), 6)
        for row in rows:
            self.assertIn(f"#check {row['declaration']}\n", text)
            self.assertIn(f"#print axioms {row['declaration']}\n", text)
        self.assertIn("unless axioms.all allowed.contains", text)
        self.assertNotIn("import CertifiedJLFast", text)

    def test_invalid_reference_is_rejected(self):
        bad = {"result": [{"id": "bad", "lean": "X; injected",
                           "lean_owner": "CertifiedJL.lean",
                           "verification_class": "kernel_checked"}]}
        with patch.object(review.tomllib, "loads", side_effect=[bad, {}]):
            with self.assertRaisesRegex(ValueError, "invalid declaration"):
                review.entries(review.ROOT)

    def test_missing_file_is_rejected(self):
        bad = {"result": [{"id": "bad", "lean": "CertifiedJL.missing",
                           "lean_owner": "CertifiedJL/NoSuchReviewSource.lean",
                           "verification_class": "kernel_checked"}]}
        with patch.object(review.tomllib, "loads", side_effect=[bad, {}]):
            with self.assertRaisesRegex(ValueError, "missing source"):
                review.entries(review.ROOT)


if __name__ == "__main__":
    unittest.main()
