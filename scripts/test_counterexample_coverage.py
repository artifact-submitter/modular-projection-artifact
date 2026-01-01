#!/usr/bin/env python3
"""Tests for deterministic counterexample coverage rendering."""

import unittest

from counterexample_catalog import load_catalogs
from render_counterexample_coverage import render_markdown, render_tsv, rendered_documents


class CoverageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.catalogs = load_catalogs()

    def test_rendering_is_deterministic_and_committed(self):
        first = rendered_documents()
        second = rendered_documents()
        self.assertEqual(first, second)
        for path, content in first.items():
            self.assertEqual(path.read_text(encoding="utf-8"), content)

    def test_exact_information_is_not_rounded_away(self):
        markdown = render_markdown(self.catalogs)
        for expected in ("(0, 9/4]", "(3/2) * 2^-130", "129.415037499279",
                         "upper `509` at 264 rows and 192 bits",
                         "coordinate upper `1358/100` at 462 rows and 256 bits",
                         "floor `76` failures at 192 and 193 bits"):
            self.assertIn(expected, markdown)
        for declaration in ("CertifiedJL.affineL2UpperTailAt_iff",
                            "CertifiedJL.sparseRademacherMatrix_eventProbability_allRows_eq_prod",
                            "CertifiedJL.sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_pow"):
            self.assertIn(declaration, markdown)

    def test_every_authoritative_source_has_one_tsv_row(self):
        rows = render_tsv(self.catalogs).splitlines()
        self.assertEqual(len(rows), 1 + len(self.catalogs.results["result"]) + len(self.catalogs.contract["claim"]))
        source_ids = [row.split("\t", 2)[1] for row in rows[1:]]
        self.assertEqual(len(source_ids), len(set(source_ids)))


if __name__ == "__main__":
    unittest.main()
