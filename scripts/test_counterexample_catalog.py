#!/usr/bin/env python3
"""Mutation tests for the counterexample evidence contract."""

from copy import deepcopy
from fractions import Fraction
import unittest

from counterexample_catalog import CatalogError, load_catalogs, require_unique
from check_counterexample_catalog import (
    check_claim_consequences, check_comparisons, check_derivations,
    check_families, check_witnesses,
)


class CatalogTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.catalogs = load_catalogs()
        cls.results = require_unique(cls.catalogs.results["result"], "id", "result")
        cls.claims = require_unique(cls.catalogs.contract["claim"], "id", "claim")
        cls.families, cls.rules = check_families(cls.catalogs.families)
        cls.witnesses = check_witnesses(cls.catalogs.witnesses, cls.families, cls.claims)

    def test_complete_baseline_coverage_without_duplicate_upper_units(self):
        comparisons = check_comparisons(
            self.catalogs.comparisons, self.results, self.claims, self.witnesses, self.rules
        )
        self.assertEqual(len(self.results), 96)
        self.assertEqual(len(self.claims), 21)
        self.assertEqual(len([c for c in comparisons.values() if c.get("result_ids")]), 80)
        self.assertEqual(sum(len(c.get("result_ids", [])) for c in comparisons.values()), 96)
        self.assertEqual(sum(c.get("setting_relation") == "same_optimum_zero_mask" for c in comparisons.values()), 16)
        paired = [c for c in comparisons.values() if c.get("setting_relation") == "same_optimum_zero_mask"]
        self.assertTrue(all(c["positive_verification_class"] == "kernel_checked" for c in paired))
        self.assertTrue(all(c["verification_class"] == "replay_pending" for c in paired))
        self.assertTrue(all(c["rule_ids"] == ["upper-mask-optimum"] for c in paired))
        self.assertEqual(sum(c.get("classification") == "sampled_positive_family" for c in comparisons.values()), 22)
        check_derivations(self.catalogs.comparisons, comparisons, self.rules)
        check_claim_consequences(self.catalogs.comparisons, comparisons, self.claims, self.witnesses)

    def test_family_semantic_mutations_fail(self):
        for field, value in (
            ("row_law", "lookalike_name"), ("statistic", "modular_linf"),
            ("event_comparison", "closed_le"), ("mask_model", "arbitrary"),
            ("threshold_reference", "input_relative"), ("modulus_domain", "positive_natural"),
        ):
            document = deepcopy(self.catalogs.families)
            document["family"][0][field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_families(document)

    def test_wrong_fixed_parameter_and_source_strictness_fail(self):
        document = deepcopy(self.catalogs.comparisons)
        unit = next(c for c in document["comparison"] if c.get("result_ids"))
        unit["rows"] += 1
        with self.assertRaises(CatalogError):
            check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)
        for field in ("axis", "status", "purpose", "completion_condition"):
            document = deepcopy(self.catalogs.comparisons)
            document["comparison"][0].pop(field)
            with self.assertRaises(CatalogError, msg=field):
                check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)
        for field, value in (("axis", ["modulus"]), ("status", "optimum_attained"),
                             ("classification", "proof_complete"), ("purpose", "unrelated"),
                             ("completion_condition", "done")):
            document = deepcopy(self.catalogs.comparisons)
            document["comparison"][0][field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)
        for denominator in (None, True, 0):
            document = deepcopy(self.catalogs.comparisons)
            unit = next(c for c in document["comparison"] if c.get("result_ids"))
            if denominator is None:
                unit.pop("threshold_denominator")
            else:
                unit["threshold_denominator"] = denominator
            with self.assertRaises(CatalogError):
                check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)
        document = deepcopy(self.catalogs.comparisons)
        unit = next(c for c in document["comparison"] if c.get("result_ids"))
        unit["source_event_comparisons"] = ["closed_le"]
        with self.assertRaises(CatalogError):
            check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)

    def test_unknown_duplicate_and_deleted_ids_fail(self):
        document = deepcopy(self.catalogs.comparisons)
        document["comparison"][0]["result_ids"] = ["unknown-result"]
        with self.assertRaises(CatalogError):
            check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)
        document = deepcopy(self.catalogs.comparisons)
        duplicate = document["comparison"][0]["result_ids"][0]
        document["comparison"][1]["result_ids"].append(duplicate)
        with self.assertRaises(CatalogError):
            check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)

    def test_q9_region_and_exact_cutoff_are_locked(self):
        for field, value in (
            ("admissible_multiplier_max_numerator", "10"),
            ("event_cutoff_numerator", "465"),
            ("mask_constructor", "translated"),
        ):
            document = deepcopy(self.catalogs.witnesses)
            witness = next(w for w in document["witness"] if w["id"] == "ternary-ones16-q9-b4")
            witness[field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_witnesses(document, self.families, self.claims)
        for field, value in (("lean_implementation", "missing"),
                             ("verification_class", "kernel_checked"),
                             ("mathematical_verification_class", "kernel_checked")):
            document = deepcopy(self.catalogs.witnesses)
            witness = next(w for w in document["witness"] if w["id"] == "ternary-ones16-q9-b4")
            witness[field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_witnesses(document, self.families, self.claims)
        for path in ("/etc/hosts", "evidence/counterexamples/searches/../witnesses.toml"):
            document = deepcopy(self.catalogs.witnesses)
            witness = next(w for w in document["witness"] if w["id"] == "ternary-ones16-q9-b4")
            witness["artifact_paths"][0] = path
            with self.assertRaises(CatalogError):
                check_witnesses(document, self.families, self.claims)

    def test_upper338_reporting_factor_is_locked(self):
        for field, value in (("exact_factor_338_numerator", "999"),
                             ("exact_factor_338_denominator", "0"),
                             ("exact_factor_338_budget_bits", 999)):
            document = deepcopy(self.catalogs.witnesses)
            witness = next(w for w in document["witness"] if w["id"] == "ternary-sparse-upper-security")
            witness[field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_witnesses(document, self.families, self.claims)

    def test_singleton_checked_base_and_pending_derivations_are_distinct(self):
        singleton = self.witnesses["ternary-singleton-binomial"]
        self.assertEqual(singleton["verification_class"], "kernel_checked")
        self.assertEqual(singleton["derived_verification_class"], "replay_pending")
        self.assertEqual(len(singleton["derived_lean_declarations"]), 8)
        document = deepcopy(self.catalogs.comparisons)
        record = next(d for d in document["derived"] if d["rule_id"] == "singleton-binomial-specialization")
        record["output_budget_bits"] += 1
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)
        document = deepcopy(self.catalogs.comparisons)
        document["derived"] = [d for d in document["derived"] if d["id"] != record["id"]]
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)
        document = deepcopy(self.catalogs.comparisons)
        records = [d for d in document["derived"] if d["rule_id"] == "singleton-binomial-specialization"]
        duplicate = deepcopy(records[0])
        duplicate["id"] = "duplicate-singleton-parameters"
        document["derived"].append(duplicate)
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)
        document = deepcopy(self.catalogs.comparisons)
        record = next(d for d in document["derived"] if d["rule_id"] == "singleton-binomial-specialization")
        record["output_modulus_margin_numerator"] = 2
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)

    def test_singleton_admissibility_and_rule_identity_are_locked(self):
        document = deepcopy(self.catalogs.witnesses)
        singleton = next(w for w in document["witness"] if w["id"] == "ternary-singleton-binomial")
        singleton["parameter_domain"] = "positive integer b"
        with self.assertRaises(CatalogError):
            check_witnesses(document, self.families, self.claims)
        for field, value in (("kind", "positive_transport"), ("reference", "wrong"),
                             ("proof_status", "kernel_checked")):
            document = deepcopy(self.catalogs.families)
            rule = next(r for r in document["rule"] if r["id"] == "singleton-binomial-specialization")
            rule[field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_families(document)

    def test_f2_rule_identities_and_paired_upper_trust_are_locked(self):
        for rule_id, field, value in (
            ("upper-mask-optimum", "lean_declarations", ["wrong"]),
            ("upper-mask-optimum", "reference", "wrong"),
            ("upper-mask-optimum", "verification_class", "kernel_checked"),
            ("coordinate-lower-product", "lean_declarations", ["wrong"]),
            ("coordinate-upper-product", "generic_lean_declaration", "wrong"),
            ("coordinate-upper-product", "verification_class", "kernel_checked"),
        ):
            document = deepcopy(self.catalogs.families)
            rule = next(r for r in document["rule"] if r["id"] == rule_id)
            rule[field] = value
            with self.assertRaises(CatalogError, msg=f"{rule_id}:{field}"):
                check_families(document)
        for field, value in (("rule_ids", []), ("verification_class", "kernel_checked"),
                             ("positive_verification_class", "replay_pending")):
            document = deepcopy(self.catalogs.comparisons)
            unit = next(c for c in document["comparison"] if c.get("setting_relation") == "same_optimum_zero_mask")
            unit[field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)
        document = deepcopy(self.catalogs.comparisons)
        unit = next(c for c in document["comparison"] if not c.get("setting_relation") and c.get("result_ids"))
        unit["rule_ids"] = ["coordinate-upper-product"]
        unit["verification_class"] = "replay_pending"
        with self.assertRaises(CatalogError, msg="inapplicable rule dependency"):
            check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)

    def test_unattained_equality_does_not_create_witness(self):
        document = deepcopy(self.catalogs.witnesses)
        witness = next(w for w in document["witness"] if w["id"] == "ternary-linf-margin-one-family")
        witness["attained"] = False
        witness["refutes_strict_guarantee"] = True
        with self.assertRaises(CatalogError):
            check_witnesses(document, self.families, self.claims)

    def test_external_witness_lowers_bracket_trust(self):
        comparison = next(c for c in self.catalogs.comparisons["comparison"]
                          if c["id"] == "l2-lower-rows256-29-2128-margin-3-over-1")
        self.assertEqual(comparison["positive_verification_class"], "kernel_checked")
        self.assertEqual(comparison["verification_class"], "external_exact_artifact")
        document = deepcopy(self.catalogs.comparisons)
        mutated = next(c for c in document["comparison"] if c["id"] == comparison["id"])
        mutated["witness_verification_class"] = "kernel_checked"
        with self.assertRaises(CatalogError):
            check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)
        for field, value in (("bracket_lower_excluded_numerator", "999"),
                             ("bracket_valid_point_numerator", "4"),
                             ("positive_verification_class", "replay_pending")):
            document = deepcopy(self.catalogs.comparisons)
            mutated = next(c for c in document["comparison"] if c["id"] == comparison["id"])
            mutated[field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_comparisons(document, self.results, self.claims, self.witnesses, self.rules)

    def test_cycle_and_transitive_trust_upgrade_fail(self):
        document = deepcopy(self.catalogs.comparisons)
        first, second = document["derived"][:2]
        first["parent_ids"] = [second["id"]]
        second["parent_ids"] = [first["id"]]
        comparisons = require_unique(document["comparison"], "id", "comparison")
        with self.assertRaises(CatalogError):
            check_derivations(document, comparisons, self.rules)
        document = deepcopy(self.catalogs.comparisons)
        record = next(d for d in document["derived"] if d["verification_class"] == "kernel_checked")
        parent_id = record["parent_ids"][0]
        parent = next((c for c in document["comparison"] if c["id"] == parent_id), None)
        if parent is not None:
            parent["verification_class"] = "replay_pending"
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)

    def test_four_ninths_and_row_directions_are_exact(self):
        document = deepcopy(self.catalogs.comparisons)
        record = next(d for d in document["derived"] if d["rule_id"] == "four-ninths")
        record["output_threshold_numerator"] += 1
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)
        document = deepcopy(self.catalogs.comparisons)
        record = next(d for d in document["derived"] if d["rule_id"] == "four-ninths")
        record["output_event_comparison"] = "closed_le"
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)
        document = deepcopy(self.catalogs.comparisons)
        record = next(d for d in document["derived"] if d["rule_id"] == "row-restriction")
        record["output_rows"] = record["source_rows"] + 1
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)
        document = deepcopy(self.catalogs.comparisons)
        record = next(d for d in document["derived"] if d["rule_id"] == "row-restriction")
        record["output_family"] = "linf-upper" if record["output_family"] == "l2-upper" else "l2-upper"
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)

    def test_unimplemented_rule_and_negative_fixed_setting_fail(self):
        document = deepcopy(self.catalogs.comparisons)
        document["derived"][0]["rule_id"] = "upper-mask-optimum"
        with self.assertRaises(CatalogError):
            check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)
        for field, value in (("parent_ids", ["negative-ternary-l2-floor12"]),
                             ("output_rows", 511), ("output_threshold_numerator", 75),
                             ("output_event_comparison", "closed_le")):
            document = deepcopy(self.catalogs.comparisons)
            record = next(d for d in document["derived"] if d["rule_id"] == "budget-strengthening-negative")
            record[field] = value
            with self.assertRaises(CatalogError, msg=field):
                check_derivations(document, require_unique(document["comparison"], "id", "comparison"), self.rules)


if __name__ == "__main__":
    unittest.main()
