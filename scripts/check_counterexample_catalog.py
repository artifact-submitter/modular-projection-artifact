#!/usr/bin/env python3
"""Validate promoted counterexample records and complete source coverage."""

from __future__ import annotations

from fractions import Fraction
import hashlib
import re
from pathlib import Path
import sys

from counterexample_catalog import (
    CatalogError, FAMILY_IDS, TRUST_ORDER, canonical_unit_id, family_for_result,
    load_catalogs, rational, record_digest, require_unique, result_threshold, result_unit_key,
    source_digests, trust_min,
)
from counterexample_probability import (
    compare_dyadic_budget, identical_energy_convolution,
)
from check_three_axis_witnesses import q9_compact_certificate


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_RECIPES = {
    "binomial_cdf", "energy_convolution", "coordinate_product",
    "finite_comparison_bound", "probability_one",
}
EXPECTED_CONSTRUCTORS = {
    "explicit_vector", "constant_vector", "singleton",
    "parameterized_constructor", "parameterized_all_ones",
}
SUPPORTED_DERIVATION_RULES = {
    "four-ninths", "masked-lower-zero-mask", "row-restriction",
    "budget-strengthening-negative", "singleton-binomial-specialization",
}
EXPECTED_SINGLETON_DERIVATIONS = {
    (192, 14, 128): "CertifiedJL.Obstructions.ternaryL2ThresholdRows192Floor14Bits128False",
    (256, 13, 192): "CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor13Bits192False",
    (384, 45, 192): "CertifiedJL.Obstructions.ternaryL2ThresholdRows384Floor45Bits192False",
    (512, 59, 256): "CertifiedJL.Obstructions.ternaryL2ThresholdRows512Floor59Bits256False",
    (256, 29, 132): "CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor29Bits132False",
    (256, 9, 208): "CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor9Bits208False",
    (384, 43, 197): "CertifiedJL.Obstructions.ternaryL2ThresholdRows384Floor43Bits197False",
    (512, 57, 261): "CertifiedJL.Obstructions.ternaryL2ThresholdRows512Floor57Bits261False",
}
EXPECTED_F2_RULES = {
    "upper-mask-optimum": {
        "kind": "optimization_equivalence",
        "reference": "exact reverse zero-mask equivalences for additive-radius upper schemas",
        "lean_declarations": ["CertifiedJL.affineL2UpperTailAt_iff", "CertifiedJL.affineLInfUpperTailAt_iff"],
        "proof_status": "lean_checked_replay_pending", "verification_class": "replay_pending",
    },
    "coordinate-lower-product": {
        "kind": "independent_rows",
        "reference": "exact all-row products for varying and identical fixed masks",
        "lean_declarations": ["CertifiedJL.sparseRademacherMatrix_eventProbability_allRows_eq_prod", "CertifiedJL.sparseRademacherMatrix_eventProbability_allRows_eq_pow"],
        "proof_status": "lean_checked", "verification_class": "kernel_checked",
    },
    "coordinate-upper-product": {
        "kind": "independent_rows",
        "reference": "exact some-row complements for varying and identical events",
        "lean_declarations": ["CertifiedJL.sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_prod", "CertifiedJL.sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_pow"],
        "generic_lean_declaration": "CertifiedJL.eventProbability_iIndepFun_exists_eq_one_sub_prod",
        "proof_status": "lean_checked_replay_pending", "verification_class": "replay_pending",
    },
}
EXPECTED_FAMILY_SEMANTICS = {
    "l2-lower": ("modular_l2_squared", "lower", "strict_lt", "centered_integer_vector", "positive_odd", "public_input_threshold_squared", "zero"),
    "masked-l2-lower": ("affine_modular_l2_squared", "lower", "strict_lt", "centered_integer_vector", "positive_odd", "public_input_threshold_squared", "integer_vector_fixed_before_matrix"),
    "linf-lower": ("modular_linf", "lower", "closed_le", "centered_integer_vector", "positive_odd", "public_input_threshold", "zero"),
    "masked-linf-lower": ("affine_modular_linf", "lower", "closed_le", "centered_integer_vector", "positive_odd", "public_input_threshold", "integer_vector_fixed_before_matrix"),
    "l2-upper": ("modular_l2_squared", "upper", "strict_gt", "integer_vector", "natural_unrestricted", "input_squared_norm", "zero_or_additive_radius"),
    "linf-upper": ("modular_linf", "upper", "strict_gt", "integer_vector", "natural_unrestricted", "input_euclidean_norm", "zero_or_additive_radius"),
}


def fail(message: str) -> None:
    raise CatalogError(message)


def exact_int_fraction(record: dict, prefix: str) -> Fraction:
    numerator, denominator = record.get(f"{prefix}_numerator"), record.get(f"{prefix}_denominator")
    if isinstance(numerator, bool) or not isinstance(numerator, int):
        fail(f"{prefix}_numerator must be an integer")
    if isinstance(denominator, bool) or not isinstance(denominator, int) or denominator <= 0:
        fail(f"{prefix}_denominator must be a positive integer")
    return Fraction(numerator, denominator)


def check_families(document: dict) -> tuple[dict, dict]:
    if document.get("schema_version") != 1:
        fail("families.toml schema_version must be 1")
    families = require_unique(document.get("family", []), "id", "family")
    if set(families) != FAMILY_IDS:
        fail(f"six-family inventory mismatch: missing={sorted(FAMILY_IDS-set(families))}, extra={sorted(set(families)-FAMILY_IDS)}")
    rules = require_unique(document.get("rule", []), "id", "implication rule")
    for family in families.values():
        if family.get("row_law") != "balanced_ternary":
            fail(f"family {family['id']} has the wrong row law")
        if family.get("event_comparison") not in {"strict_lt", "closed_le", "strict_gt"}:
            fail(f"family {family['id']} has an invalid event comparison")
        fields = ("statistic", "tail", "event_comparison", "input_domain", "modulus_domain", "threshold_reference", "mask_model")
        actual = tuple(family.get(field) for field in fields)
        if actual != EXPECTED_FAMILY_SEMANTICS[family["id"]]:
            fail(f"family {family['id']} normalized semantics mismatch: {dict(zip(fields, actual))}")
        if family.get("canonical_research_family") != f"ternary-{family['id']}":
            fail(f"family {family['id']} has the wrong canonical research family")
        dangling = set(family.get("reduction_rule_ids", [])) - set(rules)
        if dangling:
            fail(f"family {family['id']} has unknown implication rules: {sorted(dangling)}")
    singleton_rule = rules.get("singleton-binomial-specialization", {})
    if (singleton_rule.get("kind"), singleton_rule.get("reference"), singleton_rule.get("proof_status")) != (
        "negative_family_specialization",
        "CertifiedJL.Obstructions.ternaryL2SingletonThresholdFalseOfScaled",
        "lean_checked_replay_pending",
    ):
        fail("singleton specialization rule identity/status changed")
    for rule_id, expected in EXPECTED_F2_RULES.items():
        rule = rules.get(rule_id, {})
        for field, value in expected.items():
            if rule.get(field) != value:
                fail(f"F2 rule {rule_id} changed {field}")
    return families, rules


def check_witnesses(document: dict, families: dict, claims: dict) -> dict:
    if document.get("schema_version") != 1:
        fail("witnesses.toml schema_version must be 1")
    witnesses = require_unique(document.get("witness", []), "id", "witness")
    covered_claims: set[str] = set()
    for witness in witnesses.values():
        if witness.get("purpose") not in {"parameter_bound", "literature_refutation", "structural_impossibility"}:
            fail(f"witness {witness['id']} has an invalid purpose")
        if witness.get("constructor") not in EXPECTED_CONSTRUCTORS:
            fail(f"witness {witness['id']} has an invalid constructor")
        if witness.get("recipe") not in EXPECTED_RECIPES:
            fail(f"witness {witness['id']} has an invalid recipe")
        family = witness.get("family")
        if family is not None and family not in families:
            fail(f"witness {witness['id']} has unknown family {family}")
        if family is None and witness.get("category") not in {"literature_refutation", "structural_impossibility"}:
            fail(f"non-quantitative witness {witness['id']} lacks an explicit category")
        verification = witness.get("verification_class")
        if verification not in TRUST_ORDER:
            fail(f"witness {witness['id']} has invalid verification_class")
        for claim_id in witness.get("claim_ids", []):
            if claim_id not in claims:
                fail(f"witness {witness['id']} references unknown claim {claim_id}")
            if claim_id in covered_claims:
                fail(f"claim {claim_id} is assigned to duplicate witness families")
            covered_claims.add(claim_id)
            if TRUST_ORDER[verification] > TRUST_ORDER[claims[claim_id]["verification_class"]]:
                fail(f"witness {witness['id']} outranks claim {claim_id}")

        if witness.get("probability_relation") == "equal" and witness.get("refutes_strict_guarantee") is True and witness.get("attained") is not True:
            fail(f"unattained equality in {witness['id']} cannot manufacture a strict-guarantee witness")
        artifact_paths, artifact_hashes = witness.get("artifact_paths", []), witness.get("artifact_sha256", [])
        if len(artifact_paths) != len(artifact_hashes):
            fail(f"witness {witness['id']} has mismatched artifact paths and hashes")
        for artifact_path, expected_hash in zip(artifact_paths, artifact_hashes):
            relative = Path(artifact_path)
            if (relative.is_absolute() or ".." in relative.parts or
                relative.parts[:3] != ("evidence", "counterexamples", "searches") or
                re.fullmatch(r"[0-9a-f]{64}", expected_hash or "") is None):
                fail(f"witness {witness['id']} artifact path/hash is not a normalized retained-search reference")
            path = (ROOT / relative).resolve()
            if not path.is_relative_to(ROOT.resolve()) or not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected_hash:
                fail(f"witness {witness['id']} artifact is missing or stale: {artifact_path}")

    if covered_claims != set(claims):
        fail(f"promoted witnesses do not cover every claim: {sorted(set(claims)-covered_claims)}")

    q9 = witnesses.get("ternary-ones16-q9-b4")
    if not q9:
        fail("required q9 witness is absent")
    if rational(q9, "admissible_multiplier_max") != Fraction(9, 4) or q9.get("admissible_multiplier_max_included") is not True:
        fail("q9 witness must preserve every rational multiplier M <= 9/4")
    if (q9.get("family"), q9.get("row_law"), q9.get("purpose"), q9.get("constructor"),
        q9.get("vector_value"), q9.get("mask_constructor"), q9.get("rows")) != (
        "l2-lower", "balanced_ternary", "parameter_bound", "constant_vector", 1, "zero", 256
    ):
        fail("q9 witness family/law/constructor/mask semantics changed")
    expected_q9_lean = (
        "CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor29MarginAtMostNineFourthsBits128False",
        "CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor29MarginTwoBits128False",
        "CertifiedJL/Projection/Counterexamples/L2Lower/TernaryL2Rows256MarginTwo.lean",
        "withheld-for-anonymous-review",
        "replay_pending",
        "external_exact_artifact",
    )
    actual_q9_lean = (
        q9.get("lean_implementation"), q9.get("lean_specialization"), q9.get("lean_owner"),
        q9.get("lean_source_commit"), q9.get("verification_class"),
        q9.get("mathematical_verification_class"),
    )
    if actual_q9_lean != expected_q9_lean:
        fail("q9 Lean/external evidence identity or replay-pending status changed")
    if q9.get("lean_axioms") != ["propext", "Classical.choice", "Quot.sound"] or len(q9.get("lean_validation_references", [])) != 3:
        fail("q9 focused Lean validation/axiom evidence changed")
    if rational(q9, "public_threshold") != 4 or q9.get("modulus") != 9 or q9.get("dimension") != 16:
        fail("q9 witness fixed parameters changed")
    energies = q9.get("energy_values", [])
    weights = q9.get("energy_weights", [])
    if len(energies) != len(weights) or any(not isinstance(value, str) or not value.isdigit() for value in weights):
        fail("q9 energy recipe has malformed exact weights")
    if len(set(energies)) != len(energies) or any(isinstance(value, bool) or not isinstance(value, int) or value < 0 for value in energies):
        fail("q9 energy support must contain distinct nonnegative integers")
    row = dict(zip(energies, map(int, weights)))
    if sum(row.values()) != 2**32:
        fail("q9 row recipe has the wrong total mass")
    cutoff = rational(q9, "event_cutoff")
    if cutoff != 29 * rational(q9, "public_threshold") ** 2 or q9.get("event_comparison") != "strict_lt":
        fail("q9 witness must use its exact strict integer cutoff")
    distribution = identical_energy_convolution(row, q9["rows"], cutoff.numerator - 1)
    probability = Fraction(sum(distribution.values()), sum(row.values()) ** q9["rows"])
    if not compare_dyadic_budget(probability, q9["budget_bits"], "strict_lt"):
        fail("q9 exact recipe does not refute its strict budget")
    try:
        q9_compact_certificate()
    except RuntimeError as error:
        fail(str(error))

    singleton = witnesses.get("ternary-singleton-binomial")
    if not singleton or (singleton.get("family"), singleton.get("row_law"), singleton.get("constructor"),
                         singleton.get("dimension"), singleton.get("mask_constructor"), singleton.get("recipe"),
                         singleton.get("event_comparison"), singleton.get("attained")) != (
                         "l2-lower", "balanced_ternary", "singleton", 1, "zero", "binomial_cdf", "strict_lt", True):
        fail("singleton witness normalized semantics changed")
    if (singleton.get("rows"), singleton.get("public_threshold_numerator"),
        singleton.get("public_threshold_denominator"), singleton.get("modulus_domain"),
        singleton.get("parameter_domain"), singleton.get("binomial_trials"),
        singleton.get("binomial_successes_max")) != (
        256, "31", "1", "every positive odd q with q >= 3b",
        "positive integer b; odd q >= 3b", 256, 30,
    ):
        fail("singleton fixed parameters or q>=3b admissibility domain changed")
    if rational(singleton, "exact_probability") != Fraction(
        1308166590463983241201143759614411993969, 2**256
    ):
        fail("singleton exact probability changed")
    if not compare_dyadic_budget(rational(singleton, "exact_probability"), 128):
        fail("singleton no longer refutes the 128-bit strict guarantee")
    expected_singleton_lean = (
        "CertifiedJL.Obstructions.ternaryL2SingletonThresholdFalseOfScaled",
        "CertifiedJL/Projection/Counterexamples/L2Lower/TernaryL2Rows256Floor31.lean",
        "withheld-for-anonymous-review",
        "replay_pending",
    )
    if (singleton.get("generic_lean_implementation"), singleton.get("derived_lean_owner"),
        singleton.get("derived_lean_source_commit"), singleton.get("derived_verification_class")) != expected_singleton_lean:
        fail("singleton generic Lean family identity or replay-pending status changed")
    if set(singleton.get("derived_lean_declarations", [])) != set(EXPECTED_SINGLETON_DERIVATIONS.values()):
        fail("singleton derived Lean declaration inventory changed")
    if singleton.get("verification_class") != "kernel_checked" or singleton.get("derived_lean_axioms") != ["propext", "Classical.choice", "Quot.sound"]:
        fail("singleton checked base or derived axiom evidence changed")
    sparse_security = witnesses.get("ternary-sparse-upper-security")
    if not sparse_security or rational(sparse_security, "exact_factor_338") != Fraction(3, 2):
        fail("threshold-338 witness must preserve the exact factor 3/2")
    bits = sparse_security.get("exact_factor_338_budget_bits")
    if isinstance(bits, bool) or bits != 130:
        fail("threshold-338 witness must preserve the exact 130-bit factor reference")
    return witnesses


def check_comparisons(document: dict, results: dict, claims: dict, witnesses: dict, rules: dict) -> dict:
    if document.get("schema_version") != 1:
        fail("comparisons.toml schema_version must be 1")
    result_digest, claim_digest = source_digests(list(results.values()), list(claims.values()))
    if document.get("source_result_sha256") != result_digest:
        fail("result source semantics are stale; regenerate and review comparisons")
    if document.get("source_claim_sha256") != claim_digest:
        fail("claim source semantics are stale; regenerate and review comparisons")

    comparisons = require_unique(document.get("comparison", []), "id", "comparison")
    result_seen: dict[str, str] = {}
    claim_seen: dict[str, str] = {}
    for comparison in comparisons.values():
        if "witness_verification_class" in comparison:
            fail(f"comparison {comparison['id']} duplicates witness trust instead of deriving it")
        result_ids = comparison.get("result_ids", [])
        claim_ids = comparison.get("claim_ids", [])
        if not result_ids and not claim_ids:
            fail(f"comparison {comparison['id']} has no authoritative source")
        for source_id, source, seen, label in (
            *((source_id, results, result_seen, "result") for source_id in result_ids),
            *((source_id, claims, claim_seen, "claim") for source_id in claim_ids),
        ):
            if source_id not in source:
                fail(f"comparison {comparison['id']} references unknown {label} {source_id}")
            if source_id in seen:
                fail(f"duplicate coverage for {label} {source_id}: {seen[source_id]} and {comparison['id']}")
            seen[source_id] = comparison["id"]

        witness_ids = comparison.get("witness_ids", [])
        unknown_witnesses = set(witness_ids) - set(witnesses)
        if unknown_witnesses:
            fail(f"comparison {comparison['id']} has dangling witnesses: {sorted(unknown_witnesses)}")
        if not isinstance(comparison.get("axis"), list) or not comparison["axis"] or not set(comparison["axis"]).issubset({"modulus", "norm", "security", "rows", "joint"}):
            fail(f"comparison {comparison['id']} has missing or invalid axes")
        for field in ("classification", "purpose", "completion_condition", "status"):
            if not isinstance(comparison.get(field), str) or not comparison[field]:
                fail(f"comparison {comparison['id']} has missing {field}")
        if result_ids:
            source_records = [results[source_id] for source_id in result_ids]
            keys = {result_unit_key(record) for record in source_records}
            if len(keys) != 1:
                fail(f"comparison {comparison['id']} combines distinct optimization units")
            key = keys.pop()
            if comparison.get("id") != canonical_unit_id(key):
                fail(f"comparison ID does not match normalized source parameters: {comparison['id']}")
            if comparison.get("family") != key[0]:
                fail(f"comparison {comparison['id']} has the wrong canonical family")
            expected_axes = ["modulus", "norm", "security", "joint"] if source_records[0]["tail"] == "lower" else ["norm", "security", "rows"]
            if comparison.get("axis") != expected_axes:
                fail(f"comparison {comparison['id']} changed its reviewed axis coverage")
            if comparison.get("rows") != key[1] or comparison.get("failure_budget") != key[2]:
                fail(f"comparison {comparison['id']} has wrong fixed rows or budget")
            if exact_int_fraction(comparison, "threshold") != result_threshold(source_records[0]):
                fail(f"comparison {comparison['id']} has the wrong threshold")
            expected_events = sorted({record["event_comparison"] for record in source_records})
            expected_statistics = sorted({record["statistic"] for record in source_records})
            if comparison.get("source_event_comparisons") != expected_events or comparison.get("source_statistics") != expected_statistics:
                fail(f"comparison {comparison['id']} lost source event/statistic semantics")
            dependency_classes = [record["verification_class"] for record in source_records]
            dependency_classes.extend(claims[source_id]["verification_class"] for source_id in claim_ids)
            dependency_classes.extend(
                witnesses[source_id].get("mathematical_verification_class", witnesses[source_id]["verification_class"])
                for source_id in witness_ids
            )
            rule_ids = comparison.get("rule_ids", [])
            if not isinstance(rule_ids, list) or any(not isinstance(rule_id, str) for rule_id in rule_ids):
                fail(f"comparison {comparison['id']} has malformed rule dependencies")
            if any(rule_id not in rules or rules[rule_id].get("verification_class") not in TRUST_ORDER for rule_id in rule_ids):
                fail(f"comparison {comparison['id']} has a dangling rule dependency")
            if comparison.get("setting_relation") == "same_optimum_zero_mask":
                if rule_ids != ["upper-mask-optimum"]:
                    fail(f"comparison {comparison['id']} lacks the reviewed zero-mask equivalence dependency")
            elif rule_ids:
                fail(f"comparison {comparison['id']} has an inapplicable rule dependency")
            dependency_classes.extend(rules[rule_id]["verification_class"] for rule_id in rule_ids)
            expected_trust = trust_min(dependency_classes)
            if comparison.get("verification_class") != expected_trust:
                fail(f"comparison {comparison['id']} outranks or disagrees with source trust")
            source_trust = trust_min(record["verification_class"] for record in source_records)
            if "positive_verification_class" in comparison and comparison["positive_verification_class"] != source_trust:
                fail(f"comparison {comparison['id']} misstates positive source verification")
            expected_classification = "sampled_positive_family" if source_trust == "replay_pending" else ("equivalent_setting" if len(source_records) > 1 else "independent_research_point")
            if comparison.get("classification") != expected_classification or comparison.get("purpose") != "tightness_bracket" or comparison.get("status") != "positive_bound_known":
                fail(f"comparison {comparison['id']} has misleading positive status metadata")
            if comparison.get("completion_condition") != "reviewed endpoint-aware bracket or stronger certified bound":
                fail(f"comparison {comparison['id']} changed its reviewed completion condition")
            if comparison.get("priority") not in {"headline", "catalog"}:
                fail(f"comparison {comparison['id']} has invalid positive priority")
        else:
            if not witness_ids:
                fail(f"negative comparison {comparison['id']} has no promoted witness")
            linked_claims = {claim_id for witness_id in witness_ids for claim_id in witnesses[witness_id].get("claim_ids", [])}
            if not set(claim_ids).issubset(linked_claims):
                fail(f"negative comparison {comparison['id']} claim/witness linkage mismatch")
            expected_trust = trust_min(claims[source_id]["verification_class"] for source_id in claim_ids)
            witness_trust = trust_min(witnesses[source_id]["verification_class"] for source_id in witness_ids)
            expected_trust = trust_min([expected_trust, witness_trust])
            if comparison.get("verification_class") != expected_trust:
                fail(f"negative comparison {comparison['id']} outranks its claim/witness evidence")
            if comparison.get("category") in {"literature_refutation", "structural_impossibility"}:
                if comparison.get("family") is not None:
                    fail(f"non-quantitative comparison {comparison['id']} must stay outside six families")
                expected_axes = ["joint"]
            elif comparison.get("family") not in FAMILY_IDS:
                fail(f"negative comparison {comparison['id']} lacks a valid family")
            else:
                expected_axes = ["norm", "security", "rows"] if comparison["family"] in {"l2-upper", "linf-upper"} else ["modulus", "norm", "security", "joint"]
            witness_purpose = witnesses[witness_ids[0]]["purpose"]
            if comparison.get("axis") != expected_axes or comparison.get("classification") != "negative_bound" or comparison.get("purpose") != witness_purpose or comparison.get("status") != "negative_bound_known":
                fail(f"negative comparison {comparison['id']} has misleading coverage metadata")
            if comparison.get("completion_condition") != "existing promoted obstruction retained" or comparison.get("priority") != "claim":
                fail(f"negative comparison {comparison['id']} changed priority/completion semantics")

    missing_results = sorted(set(results) - set(result_seen))
    missing_claims = sorted(set(claims) - set(claim_seen))
    if missing_results or missing_claims:
        fail(f"incomplete coverage: missing results={missing_results}, missing claims={missing_claims}")

    # The sixteen affine upper source records retain distinct event types but
    # must share exactly one optimization record with the corresponding zero-mask result.
    affine_upper = [record for record in results.values() if record["tail"] == "upper" and record["statistic"].startswith("affine_")]
    if len(affine_upper) != 16:
        fail(f"expected 16 current affine upper source records, found {len(affine_upper)}")
    for record in affine_upper:
        unit = comparisons[result_seen[record["id"]]]
        if (len(unit.get("result_ids", [])) != 2 or unit.get("setting_relation") != "same_optimum_zero_mask"
            or unit.get("rule_ids") != ["upper-mask-optimum"]
            or unit.get("positive_verification_class") != "kernel_checked"
            or unit.get("verification_class") != "replay_pending"):
            fail(f"affine upper result {record['id']} does not share its unmasked optimization setting")

    q9_unit = comparisons.get("l2-lower-rows256-29-2128-margin-3-over-1")
    q9_witness = witnesses["ternary-ones16-q9-b4"]
    if not q9_unit or q9_unit.get("witness_ids") != [q9_witness["id"]]:
        fail("q9 witness is not attached to the multiplier-three research bracket")
    if rational(q9_witness, "admissible_multiplier_max") != rational(q9_unit, "bracket_lower_excluded"):
        fail("q9 comparison endpoint disagrees with witness admissibility")
    if q9_unit.get("bracket_lower_excluded_included") is not True or rational(q9_unit, "bracket_valid_point") != 3 or q9_unit.get("bracket_valid_point_included") is not True:
        fail("q9 bracket must exclude (0,9/4] and retain the valid multiplier-three point")
    return comparisons


def check_derivations(document: dict, comparisons: dict, rules: dict) -> None:
    derivations = require_unique(document.get("derived", []), "id", "derived comparison")
    nodes = set(comparisons) | set(derivations)
    visiting: set[str] = set()
    complete: set[str] = set()

    def field(parent_id: str, name: str):
        parent = comparisons.get(parent_id) or derivations[parent_id]
        if name == "event_comparison" and "output_event_comparison" not in parent:
            events = parent.get("source_event_comparisons", [])
            return events[0] if len(events) == 1 else None
        return parent.get(f"output_{name}", parent.get(name))

    def visit(node_id: str) -> None:
        if node_id in complete or node_id in comparisons:
            return
        if node_id in visiting:
            fail(f"cyclic counterexample derivation at {node_id}")
        visiting.add(node_id)
        record = derivations[node_id]
        parents = record.get("parent_ids", [])
        if not parents or any(parent not in nodes for parent in parents):
            fail(f"derived comparison {node_id} has missing or dangling parents")
        for parent in parents:
            visit(parent)
        parent_classes = [
            (comparisons.get(parent) or derivations[parent])["verification_class"]
            for parent in parents
        ]
        if record.get("additional_verification_class") is not None:
            parent_classes.append(record["additional_verification_class"])
        if record.get("verification_class") != trust_min(parent_classes):
            fail(f"derived comparison {node_id} must inherit the weakest transitive trust")
        rule_id = record.get("rule_id")
        if rule_id not in rules or rule_id not in SUPPORTED_DERIVATION_RULES:
            fail(f"derived comparison {node_id} uses unapproved rule {rule_id}")
        transform = record.get("parameter_transform")
        if rule_id == "four-ninths":
            if transform != "modulus_margin:3->2" or record.get("output_family") != "masked-l2-lower":
                fail(f"four-ninths derivation {node_id} has an invalid transformation")
            parent = comparisons.get(parents[0]) or derivations[parents[0]]
            if parent.get("family") != "masked-l2-lower":
                fail(f"four-ninths derivation {node_id} has the wrong source family")
            source_threshold = exact_int_fraction(parent, "threshold")
            recorded_source = exact_int_fraction(record, "source_threshold")
            output_threshold = exact_int_fraction(record, "output_threshold")
            if recorded_source != source_threshold or output_threshold != Fraction(4, 9) * source_threshold:
                fail(f"four-ninths derivation {node_id} has the wrong exact threshold transformation")
            if (record.get("source_modulus_margin_numerator"), record.get("source_modulus_margin_denominator"),
                record.get("output_modulus_margin_numerator"), record.get("output_modulus_margin_denominator")) != (3, 1, 2, 1):
                fail(f"four-ninths derivation {node_id} has the wrong exact margin endpoints")
            if record.get("output_rows") != parent.get("rows") or record.get("output_failure_budget") != parent.get("failure_budget") or record.get("output_event_comparison") not in parent.get("source_event_comparisons", []):
                fail(f"four-ninths derivation {node_id} changed rows, budget, or event")
        elif rule_id == "masked-lower-zero-mask":
            if transform != "mask:universal->zero" or record.get("output_family") != "l2-lower":
                fail(f"zero-mask derivation {node_id} has an invalid transformation")
            parent_family = field(parents[0], "family")
            if parent_family != "masked-l2-lower":
                fail(f"zero-mask derivation {node_id} requires a masked L2 source")
            parent_threshold = exact_int_fraction({"x_numerator": field(parents[0], "threshold_numerator"), "x_denominator": field(parents[0], "threshold_denominator")}, "x")
            output_threshold = exact_int_fraction(record, "output_threshold")
            if output_threshold != parent_threshold or record.get("output_rows") != field(parents[0], "rows") or record.get("output_failure_budget") != field(parents[0], "failure_budget"):
                fail(f"zero-mask derivation {node_id} changed fixed threshold, rows, or budget")
            if record.get("output_event_comparison") != field(parents[0], "event_comparison"):
                fail(f"zero-mask derivation {node_id} changed event strictness")
        elif rule_id == "row-restriction":
            source_rows, output_rows = record.get("source_rows"), record.get("output_rows")
            if not isinstance(source_rows, int) or not isinstance(output_rows, int) or not (0 < output_rows <= source_rows):
                fail(f"row-restriction derivation {node_id} has an invalid row direction")
            if transform != f"rows:{source_rows}->{output_rows}":
                fail(f"row-restriction derivation {node_id} has an inconsistent transformation")
            if source_rows != field(parents[0], "rows") or record.get("output_failure_budget") != field(parents[0], "failure_budget"):
                fail(f"row-restriction derivation {node_id} changed source rows or budget")
            if exact_int_fraction(record, "output_threshold") != exact_int_fraction({"x_numerator": field(parents[0], "threshold_numerator"), "x_denominator": field(parents[0], "threshold_denominator")}, "x"):
                fail(f"row-restriction derivation {node_id} changed threshold")
            if record.get("output_family") != field(parents[0], "family") or record.get("output_event_comparison") != field(parents[0], "event_comparison"):
                fail(f"row-restriction derivation {node_id} changed family or event")
        elif rule_id == "budget-strengthening-negative":
            source_bits, output_bits = record.get("source_budget_bits"), record.get("output_budget_bits")
            if not isinstance(source_bits, int) or not isinstance(output_bits, int) or output_bits < source_bits:
                fail(f"negative budget derivation {node_id} has an invalid direction")
            if transform != f"budget_bits:{source_bits}->{output_bits}":
                fail(f"negative budget derivation {node_id} has an inconsistent transformation")
            if parents != ["negative-ternary-floor76-family"] or (source_bits, output_bits) != (192, 193):
                fail(f"negative budget derivation {node_id} is not the reviewed floor-76 consequence")
            if (record.get("output_family"), record.get("output_rows"), exact_int_fraction(record, "output_threshold"), record.get("output_event_comparison")) != ("l2-lower", 512, Fraction(76), "strict_lt"):
                fail(f"negative budget derivation {node_id} changed the floor-76 fixed setting")
        elif rule_id == "singleton-binomial-specialization":
            key = (record.get("output_rows"), record.get("output_threshold_numerator"), record.get("output_budget_bits"))
            if parents != ["negative-ternary-singleton-binomial"] or key not in EXPECTED_SINGLETON_DERIVATIONS:
                fail(f"singleton derivation {node_id} is not one of the eight reviewed parameter points")
            expected_transform = f"singleton:rows{key[0]}-floor{key[1]}-bits{key[2]}"
            if (record.get("parameter_transform"), record.get("output_family"),
                record.get("output_threshold_denominator"), record.get("output_event_comparison"),
                record.get("output_modulus_margin_numerator"), record.get("output_modulus_margin_denominator"),
                record.get("lean_declaration"), record.get("additional_verification_class")) != (
                expected_transform, "l2-lower", 1, "strict_lt", 3, 1,
                EXPECTED_SINGLETON_DERIVATIONS[key], "replay_pending"
            ):
                fail(f"singleton derivation {node_id} changed its exact transformation or Lean identity")
        visiting.remove(node_id)
        complete.add(node_id)

    for node_id in derivations:
        visit(node_id)
    singleton_keys: dict[tuple[int, int, int], str] = {}
    for record in derivations.values():
        if record.get("rule_id") != "singleton-binomial-specialization":
            continue
        key = (record.get("output_rows"), record.get("output_threshold_numerator"), record.get("output_budget_bits"))
        if key in singleton_keys:
            fail(f"duplicate singleton specialization parameters in {singleton_keys[key]} and {record['id']}")
        singleton_keys[key] = record["id"]
    if set(singleton_keys) != set(EXPECTED_SINGLETON_DERIVATIONS):
        fail(f"singleton specialization inventory mismatch: missing={sorted(set(EXPECTED_SINGLETON_DERIVATIONS)-set(singleton_keys))}, extra={sorted(set(singleton_keys)-set(EXPECTED_SINGLETON_DERIVATIONS))}")


def check_claim_consequences(document: dict, comparisons: dict, claims: dict, witnesses: dict) -> None:
    consequences = require_unique(document.get("claim_consequence", []), "id", "claim consequence")
    seen: set[str] = set()
    for consequence in consequences.values():
        claim_id = consequence.get("claim_id")
        comparison_id = consequence.get("comparison_id")
        witness_id = consequence.get("witness_id")
        if claim_id not in claims or claim_id in seen:
            fail(f"unknown or duplicate claim consequence for {claim_id}")
        seen.add(claim_id)
        if comparison_id not in comparisons or claim_id not in comparisons[comparison_id].get("claim_ids", []):
            fail(f"claim consequence {consequence['id']} has the wrong comparison")
        if witness_id not in witnesses or claim_id not in witnesses[witness_id].get("claim_ids", []):
            fail(f"claim consequence {consequence['id']} has the wrong witness family")
        if consequence.get("source_semantic_sha256") != record_digest(claims[claim_id]):
            fail(f"claim consequence {consequence['id']} is stale")
        expected_trust = trust_min([
            claims[claim_id].get("verification_class"),
            witnesses[witness_id].get("verification_class"),
        ])
        if consequence.get("verification_class") != expected_trust:
            fail(f"claim consequence {consequence['id']} outranks its claim/witness evidence")
    if seen != set(claims):
        fail(f"per-claim consequence coverage is incomplete: {sorted(set(claims)-seen)}")


def check(root: Path = ROOT) -> None:
    catalogs = load_catalogs(root)
    results = require_unique(catalogs.results.get("result", []), "id", "result")
    claims = require_unique(catalogs.contract.get("claim", []), "id", "claim")
    families, rules = check_families(catalogs.families)
    witnesses = check_witnesses(catalogs.witnesses, families, claims)
    comparisons = check_comparisons(catalogs.comparisons, results, claims, witnesses, rules)
    check_derivations(catalogs.comparisons, comparisons, rules)
    check_claim_consequences(catalogs.comparisons, comparisons, claims, witnesses)


if __name__ == "__main__":
    try:
        check()
    except CatalogError as error:
        print(f"counterexample catalog error: {error}", file=sys.stderr)
        raise SystemExit(1)
    print("Counterexample catalogs are valid and cover all authoritative results and claims.")
