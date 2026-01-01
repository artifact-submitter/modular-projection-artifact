#!/usr/bin/env python3
"""Regression tests for the intentional main-result contract boundary."""

from __future__ import annotations

import contextlib
import copy
import io
import unittest

import check_contract


class MainResultContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = {
            "id": "rows256-example",
            "rows": 256,
            "threshold_numerator": 29,
            "input_condition": "odd q; centered w; 3 * b <= q",
            "event_comparison": "strict_lt",
            "failure_budget": "2^-128",
            "lean": "Example.result",
            "lean_owner": "Example.lean",
            "verification_class": "kernel_checked",
            "certificate_ids": [],
            "paper_locator": "thm:main",
        }
        self.contract = {
            "certified_results": {
                "semantic_sha256": check_contract.semantic_result_digest([self.result])
            }
        }

    def assert_rejected(self, results: list[dict]) -> None:
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            check_contract.check_result_semantic_digest(self.contract, results)

    def test_missing_required_main_result_is_rejected(self) -> None:
        self.assert_rejected([])

    def test_changed_required_main_constant_is_rejected(self) -> None:
        changed = copy.deepcopy(self.result)
        changed["threshold_numerator"] = 30
        self.assert_rejected([changed])

    def test_changed_required_hypothesis_event_or_budget_is_rejected(self) -> None:
        for field, value in (
            ("input_condition", "odd q; centered w"),
            ("event_comparison", "closed_le"),
            ("failure_budget", "2^-127"),
        ):
            with self.subTest(field=field):
                changed = copy.deepcopy(self.result)
                changed[field] = value
                self.assert_rejected([changed])

    def test_result_record_reordering_is_semantically_invariant(self) -> None:
        other = {**self.result, "id": "rows192-example", "lean": "Example.other"}
        self.assertEqual(
            check_contract.semantic_result_digest([self.result, other]),
            check_contract.semantic_result_digest([other, self.result]),
        )

    def test_changed_substantive_claim_is_rejected(self) -> None:
        claim = {
            "id": "floor31-obstruction",
            "statement": "strict floor 31 fails for every positive b",
            "verification_class": "proof_outstanding",
            "outstanding_dependencies": ["strict event proof"],
        }
        contract = {
            "substantive_claims": {
                "semantic_sha256": check_contract.semantic_claim_digest([claim])
            }
        }
        for field, value in (
            ("statement", "closed floor 30 fails for some b"),
            ("verification_class", "kernel_checked"),
            ("outstanding_dependencies", []),
        ):
            with self.subTest(field=field):
                changed = copy.deepcopy(claim)
                changed[field] = value
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                    check_contract.check_claim_semantic_digest(contract, [changed])

    def test_claim_record_reordering_is_semantically_invariant(self) -> None:
        claims = [{"id": "b", "statement": "B"}, {"id": "a", "statement": "A"}]
        self.assertEqual(
            check_contract.semantic_claim_digest(claims),
            check_contract.semantic_claim_digest(list(reversed(claims))),
        )

    def test_counterexample_digest_excludes_unpromoted_search_logs(self) -> None:
        documents = [{"family": [{"id": "l2-lower"}]}, {"witness": []}, {"comparison": []}]
        digest = check_contract.semantic_counterexample_digest(documents)
        # Unpromoted search state is deliberately not an input to this function.
        self.assertEqual(digest, check_contract.semantic_counterexample_digest(copy.deepcopy(documents)))
        changed = copy.deepcopy(documents)
        changed[0]["family"][0]["event"] = "closed_le"
        self.assertNotEqual(digest, check_contract.semantic_counterexample_digest(changed))

    def test_counterexample_record_reordering_is_semantically_invariant(self) -> None:
        documents = [{"family": [{"id": "b", "tail": "upper"}, {"id": "a", "tail": "lower"}]}]
        reordered = copy.deepcopy(documents)
        reordered[0]["family"].reverse()
        self.assertEqual(
            check_contract.semantic_counterexample_digest(documents),
            check_contract.semantic_counterexample_digest(reordered),
        )

    def test_changed_headline_inventory_is_rejected(self) -> None:
        results = [{"id": value} for value in check_contract.EXPECTED_HEADLINE_IDS]
        valid = {"headline_results": {"result_ids": sorted(check_contract.EXPECTED_HEADLINE_IDS)}}
        check_contract.check_headline_inventory(valid, results)
        invalid = copy.deepcopy(valid)
        invalid["headline_results"]["result_ids"].pop()
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            check_contract.check_headline_inventory(invalid, results)

    def test_explanatory_lemma_edits_create_no_lean_obligation(self) -> None:
        claim = {
            "id": "outstanding-main-claim",
            "role": "negative_result",
            "statement": "Exact required statement.",
            "paper_source": "main.tex",
            "paper_locator": "thm:main",
            "verification_class": "proof_outstanding",
            "lean": "",
            "analytic_owner": "",
            "certificate_dependencies": [],
            "validation_evidence": [],
            "public_canary": "",
            "outstanding_dependencies": ["exact proof"],
        }
        before = {"main.tex": r"\begin{theorem}\label{thm:main}M\end{theorem}"}
        after = {
            "main.tex": before["main.tex"]
            + r"\begin{lemma}\label{lem:renamed-explanation}E\end{lemma}"
        }
        check_contract.check_claims([claim], before, [])
        check_contract.check_claims([claim], after, [])


if __name__ == "__main__":
    unittest.main()
