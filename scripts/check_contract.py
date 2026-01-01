#!/usr/bin/env python3
"""Validate the stable main-result contract and its paper snapshot."""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

from lean_source import LeanSourceError, qualified_declarations


ROOT = Path(__file__).resolve().parents[1]
PAPER_ROOT = ROOT / "paper"
CONTRACT_PATH = ROOT / "evidence" / "theorem-contract.toml"
SNAPSHOT_PATH = ROOT / "evidence" / "paper-snapshot.toml"
RESULT_PATH = ROOT / "evidence" / "result-catalog.toml"
API_PATH = ROOT / "evidence" / "public-api.toml"
CERTIFICATE_PATH = ROOT / "evidence" / "certificates" / "public-results.toml"
REPLAY_PATH = ROOT / "evidence" / "certificates" / "replay-families.toml"
COUNTEREXAMPLE_PATHS = (
    ROOT / "evidence" / "counterexamples" / "families.toml",
    ROOT / "evidence" / "counterexamples" / "witnesses.toml",
    ROOT / "evidence" / "counterexamples" / "comparisons.toml",
)
CHECKED_CLASSES = {"kernel_checked", "native_attested", "replay_pending"}
ALLOWED_CLAIM_CLASSES = CHECKED_CLASSES | {
    "explicit_assumption_reduction",
    "external_exact_artifact",
    "proof_outstanding",
}
ALLOWED_CLAIM_ROLES = {"negative_result", "headline_result", "parameter_family"}
EXPECTED_HEADLINE_IDS = {
    "rows256-ternary-l2-threshold-lower-29-bits128",
    "rows256-ternary-affine-l2-threshold-lower-27-bits128",
    "rows256-ternary-linf-threshold-lower-21-over-50-bits133",
    "rows256-ternary-affine-linf-threshold-lower-67-over-200-bits130",
    "rows256-ternary-l2-upper-338-bits128",
    "rows256-ternary-linf-upper-39-over-4-bits133",
}
EXPECTED_PAPER_PARAMETERS = {
    "rows": 256,
    "security_bits": 128,
    "orthus_security_bits": 133,
    "ternary_lower": 29,
    "ternary_upper": 338,
    "ternary_threshold_margin_numerator": 3,
    "ternary_threshold_margin_denominator": 1,
    "ternary_upper_disproved": 336,
    "orthus_infinity_numerator": 21,
    "orthus_infinity_denominator": 50,
    "orthus_threshold_margin_numerator": 2,
    "orthus_threshold_margin_denominator": 1,
    "orthus_extraction_slack_numerator": 325,
    "orthus_extraction_slack_denominator": 14,
    "orthus_modulus_coefficient_numerator": 325,
    "orthus_modulus_coefficient_denominator": 7,
}


def fail(message: str) -> None:
    print(f"contract error: {message}", file=sys.stderr)
    raise SystemExit(1)


def load(path: Path) -> dict:
    with path.open("rb") as source:
        return tomllib.load(source)


def require_unique(records: list[dict], field: str, label: str) -> None:
    values = [record.get(field) for record in records]
    if any(not value for value in values):
        fail(f"every {label} must define nonempty {field!r}")
    duplicates = sorted(value for value in set(values) if values.count(value) > 1)
    if duplicates:
        fail(f"duplicate {label} {field} values: {duplicates}")


def semantic_result_digest(results: list[dict]) -> str:
    """Hash the exact advertised-result records, independent of TOML layout."""
    payload = json.dumps(
        sorted(results, key=lambda record: record["id"]),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def check_result_semantic_digest(contract: dict, results: list[dict]) -> None:
    expected_digest = contract.get("certified_results", {}).get("semantic_sha256", "")
    actual_digest = semantic_result_digest(results)
    if expected_digest != actual_digest:
        fail(
            "advertised-result semantics changed without main-ledger review: "
            f"expected {expected_digest}, found {actual_digest}"
        )


def semantic_claim_digest(claims: list[dict]) -> str:
    """Hash substantive claims independently of TOML record order."""
    payload = json.dumps(
        sorted(claims, key=lambda record: record["id"]),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def check_claim_semantic_digest(contract: dict, claims: list[dict]) -> None:
    expected_digest = contract.get("substantive_claims", {}).get("semantic_sha256", "")
    actual_digest = semantic_claim_digest(claims)
    if expected_digest != actual_digest:
        fail(
            "substantive claim semantics changed without main-ledger review: "
            f"expected {expected_digest}, found {actual_digest}"
        )


def semantic_counterexample_digest(documents: list[dict]) -> str:
    """Hash promoted records/rules, excluding exploratory search logs."""
    def normalize(value):
        if isinstance(value, dict):
            return {key: normalize(item) for key, item in value.items()}
        if isinstance(value, list):
            normalized = [normalize(item) for item in value]
            if all(isinstance(item, dict) and isinstance(item.get("id"), str) for item in normalized):
                return sorted(normalized, key=lambda item: item["id"])
            return normalized
        return value

    payload = json.dumps(
        normalize(documents),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def check_counterexample_evidence_digest(contract: dict) -> None:
    ledger = contract.get("counterexample_evidence", {})
    expected_paths = [str(path.relative_to(ROOT)) for path in COUNTEREXAMPLE_PATHS]
    recorded_paths = [ledger.get("families"), ledger.get("witnesses"), ledger.get("comparisons")]
    if recorded_paths != expected_paths:
        fail("counterexample evidence paths differ from the promoted three-catalog boundary")
    if ledger.get("semantic_hash") != "sha256-canonical-json-v1":
        fail("counterexample evidence must use the canonical JSON digest")
    actual = semantic_counterexample_digest([load(path) for path in COUNTEREXAMPLE_PATHS])
    if ledger.get("semantic_sha256") != actual:
        fail(
            "promoted counterexample evidence or implication rules changed without ledger review: "
            f"expected {ledger.get('semantic_sha256')}, found {actual}"
        )
    for field in ("generated_markdown", "generated_tsv"):
        path = ledger.get(field)
        if not isinstance(path, str) or not (ROOT / path).is_file():
            fail(f"counterexample evidence has missing {field}")


def check_headline_inventory(contract: dict, results: list[dict]) -> None:
    headline_ids = contract.get("headline_results", {}).get("result_ids", [])
    if len(headline_ids) != len(set(headline_ids)):
        fail("headline result IDs must be unique")
    if set(headline_ids) != EXPECTED_HEADLINE_IDS:
        fail(
            "headline result inventory differs from the reviewed six IDs: "
            f"missing={sorted(EXPECTED_HEADLINE_IDS - set(headline_ids))}, "
            f"extra={sorted(set(headline_ids) - EXPECTED_HEADLINE_IDS)}"
        )
    result_ids = {result["id"] for result in results}
    missing = sorted(set(headline_ids) - result_ids)
    if missing:
        fail(f"headline results are absent from the advertised inventory: {missing}")


def check_snapshot(snapshot: dict) -> dict[str, str]:
    """Pin reviewed paper bytes without inventorying explanatory environments."""
    if snapshot.get("paper_commit_tree_clean") is not True:
        fail("paper snapshot must point to a committed clean paper tree")
    paper_head = snapshot.get("paper_git_head", "")
    if re.fullmatch(r"[0-9a-f]{40}", paper_head) is None:
        fail("invalid paper snapshot commit")
    prefix = snapshot.get("paper_git_prefix", "")
    if not isinstance(prefix, str):
        fail("paper_git_prefix must be a string")
    try:
        subprocess.run(
            ["git", "-C", str(ROOT), "cat-file", "-e", f"{paper_head}^{{commit}}"],
            check=True,
            capture_output=True,
        )
    except subprocess.CalledProcessError:
        fail(f"pinned paper commit is unavailable: {paper_head}")

    pinned: dict[str, str] = {}
    seen_paths: set[str] = set()
    for category in ("source", "context", "artifact"):
        records = snapshot.get(category, [])
        if not records:
            fail(f"paper snapshot has no {category} records")
        for record in records:
            path = record.get("path", "")
            digest = record.get("sha256", "")
            if not path or path in seen_paths:
                fail(f"missing or duplicate paper snapshot path: {path!r}")
            seen_paths.add(path)
            if re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                fail(f"invalid paper snapshot digest: {path}")
            git_path = f"{prefix}/{path}" if prefix else path
            try:
                data = subprocess.check_output(
                    ["git", "-C", str(ROOT), "show", f"{paper_head}:{git_path}"]
                )
            except subprocess.CalledProcessError:
                fail(f"pinned paper file is unavailable: {git_path}")
            if hashlib.sha256(data).hexdigest() != digest:
                fail(f"pinned paper digest mismatch: {path}")
            current = PAPER_ROOT / path
            if not current.is_file() or hashlib.sha256(current.read_bytes()).hexdigest() != digest:
                fail(f"current paper file differs from pinned snapshot: {path}")
            pinned[path] = data.decode("utf-8")
    return pinned


def check_lean_declarations(records: list[dict]) -> None:
    """Resolve every checked declaration, including replay-pending ones."""
    cache: dict[str, set[str]] = {}
    for record in records:
        if record["verification_class"] not in CHECKED_CLASSES:
            continue
        owner = record.get("analytic_owner") or record.get("lean_owner")
        path = ROOT / owner
        if not path.is_file():
            fail(f"Lean declaration owner is absent: {owner}")
        if owner not in cache:
            try:
                cache[owner] = qualified_declarations(path.read_text(), owner)
            except LeanSourceError as error:
                fail(str(error))
        if record["lean"] not in cache[owner]:
            fail(f"Lean declaration is absent: {record['lean']} in {owner}")


def check_result_parameter_binding(parameters: dict, results: list[dict]) -> None:
    """Bind the headlines to their exact rows, budgets, events, and margins."""
    matrix_results = [
        result
        for result in results
        if result.get("statistic") == "modular_l2_squared"
        and result.get("rows") == parameters["rows"]
        and result.get("failure_budget") == f"2^-{parameters['security_bits']}"
    ]
    if not matrix_results:
        fail("result catalog has no modular Euclidean results at the paper target")

    def headline_threshold(row_law: str, tail: str) -> Fraction:
        candidates = [
            result
            for result in matrix_results
            if result.get("row_law") == row_law
            and result.get("tail") == tail
            and (
                result.get("input_norm_cap_kind") == "unrestricted"
                if tail == "upper"
                else result.get("input_norm_cap_kind") == "public_threshold_over_modulus"
            )
        ]
        if not candidates:
            fail(f"missing {row_law} modular Euclidean {tail} result")
        try:
            thresholds = [
                Fraction(result["threshold_numerator"], result["threshold_denominator"])
                for result in candidates
            ]
            return max(thresholds) if tail == "lower" else min(thresholds)
        except (KeyError, TypeError, ZeroDivisionError) as error:
            fail(f"invalid threshold in {row_law} modular Euclidean {tail} result: {error}")

    bindings = {
        "ternary_lower": headline_threshold("balanced_ternary", "lower"),
        "ternary_upper": headline_threshold("balanced_ternary", "upper"),
    }
    for parameter, cataloged in bindings.items():
        if Fraction(parameters[parameter]) != cataloged:
            fail(
                f"paper parameter {parameter}={parameters[parameter]} "
                f"disagrees with strongest cataloged result {cataloged}"
            )

    threshold_results = [
        result
        for result in matrix_results
        if result.get("row_law") == "balanced_ternary"
        and result.get("tail") == "lower"
        and result.get("input_norm_cap_kind") == "public_threshold_over_modulus"
        and result.get("threshold_numerator") == parameters["ternary_lower"]
        and result.get("threshold_denominator") == 1
    ]
    if len(threshold_results) != 1:
        fail("result catalog must contain exactly one 128-bit ternary L2 threshold result")
    threshold = threshold_results[0]
    if (
        threshold.get("input_threshold_relation") != "b^2 <= sqNorm(w)"
        or threshold.get("modulus_margin_numerator")
        != parameters["ternary_threshold_margin_numerator"]
        or threshold.get("modulus_margin_denominator")
        != parameters["ternary_threshold_margin_denominator"]
        or threshold.get("event_comparison") != "strict_lt"
        or threshold.get("probability_comparison") != "strict_lt"
        or threshold.get("input_condition")
        != "odd q; centered integer vector w; positive natural threshold b; b^2 <= sqNorm(w); 3 * b <= q"
    ):
        fail("ternary L2 threshold headline changed its hypotheses or strict event")

    orthus_results = [
        result
        for result in results
        if result.get("row_law") == "balanced_ternary"
        and result.get("statistic") == "modular_linf"
        and result.get("tail") == "lower"
        and result.get("rows") == parameters["rows"]
        and result.get("coordinate_cap_numerator") == parameters["orthus_infinity_numerator"]
        and result.get("coordinate_cap_denominator") == parameters["orthus_infinity_denominator"]
        and result.get("failure_budget") == f"2^-{parameters['orthus_security_bits']}"
    ]
    if len(orthus_results) != 1:
        fail("result catalog must contain exactly one primary Orthus infinity result")
    orthus = orthus_results[0]
    if (
        orthus.get("input_norm_cap_kind") != "public_threshold_over_modulus"
        or orthus.get("input_threshold_relation") != "b^2 <= sqNorm(w)"
        or orthus.get("modulus_margin_numerator")
        != parameters["orthus_threshold_margin_numerator"]
        or orthus.get("modulus_margin_denominator")
        != parameters["orthus_threshold_margin_denominator"]
        or orthus.get("event_comparison") != "closed_le"
        or orthus.get("probability_comparison") != "strict_lt"
        or orthus.get("input_condition")
        != "odd q; centered integer vector w; positive natural threshold b; b^2 <= sqNorm(w); 2 * b <= q"
    ):
        fail("Orthus infinity headline changed its hypotheses or closed event")

    for result in matrix_results:
        if result.get("tail") == "upper" and result.get("input_condition") != (
            "every natural q and integer vector w; no norm restriction"
        ):
            fail(f"upper result retains stale modulus/vector premises: {result['id']}")


def check_catalog_links(
    contract: dict,
    results: list[dict],
    api: list[dict],
    certificates: list[dict],
    replay_families: list[dict],
) -> None:
    check_result_semantic_digest(contract, results)
    require_unique(results, "id", "advertised result")
    require_unique(results, "lean", "advertised result")
    api_by_name = {record.get("name"): record for record in api}
    if len(api_by_name) != len(api):
        fail("public API contains duplicate declaration names")
    certificate_by_group: dict[str, list[dict]] = {}
    for certificate in certificates:
        certificate_by_group.setdefault(certificate.get("group_id", ""), []).append(certificate)
    replay_certificate_ids = {
        certificate_id
        for family in replay_families
        for certificate_id in family.get("certificate_ids", [])
    }
    for result in results:
        if result["verification_class"] not in CHECKED_CLASSES:
            fail(f"advertised result has unsupported proof status: {result['id']}")
        api_record = api_by_name.get(result["lean"])
        if api_record is None or api_record.get("owner") != result["lean_owner"]:
            fail(f"advertised result lacks its exact public API owner/canary: {result['id']}")
        for group_id in result.get("certificate_ids", []):
            providers = certificate_by_group.get(group_id, [])
            if not providers:
                fail(f"advertised result has unregistered dependency {group_id}: {result['id']}")
            missing_replays = sorted(
                provider["id"]
                for provider in providers
                if provider["id"] not in replay_certificate_ids
            )
            if missing_replays:
                fail(f"certificate dependencies lack replay roots: {missing_replays}")
        if result["verification_class"] == "replay_pending" and not result.get("certificate_ids"):
            fail(f"replay-pending result has no registered dependency closure: {result['id']}")
    check_lean_declarations(results)


def check_claims(claims: list[dict], paper: dict[str, str], api: list[dict]) -> None:
    # Freeze exact constants, events, quantifiers, statuses, and closure plans.
    # This check precedes the structural checks so an edited claim cannot pass
    # merely because it remains well formed.
    require_unique(claims, "id", "main claim")
    api_by_name = {record.get("name"): record for record in api}
    required = {
        "id", "role", "statement", "paper_source", "paper_locator",
        "verification_class", "lean", "analytic_owner", "certificate_dependencies",
        "validation_evidence", "public_canary", "outstanding_dependencies",
    }
    for claim in claims:
        missing = sorted(required - set(claim))
        if missing:
            fail(f"main claim {claim.get('id')} misses fields: {missing}")
        if re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", claim["id"]) is None:
            fail(f"invalid stable main-claim ID: {claim['id']}")
        if claim["role"] not in ALLOWED_CLAIM_ROLES:
            fail(f"invalid role for {claim['id']}: {claim['role']}")
        if claim["verification_class"] not in ALLOWED_CLAIM_CLASSES:
            fail(f"invalid proof status for {claim['id']}: {claim['verification_class']}")
        source = paper.get(claim["paper_source"])
        if source is None or claim["paper_locator"] not in source:
            fail(f"main claim has no pinned paper location: {claim['id']}")
        for path in claim.get("external_evidence", []):
            if not (ROOT / path).is_file():
                fail(f"main claim external evidence is absent: {claim['id']}: {path}")
        if claim["verification_class"] == "proof_outstanding":
            if claim["lean"] or claim["analytic_owner"] or claim["public_canary"]:
                fail(f"outstanding claim must not advertise a Lean declaration: {claim['id']}")
            if not claim["outstanding_dependencies"]:
                fail(f"outstanding claim has no exact closure plan: {claim['id']}")
            continue
        if claim["outstanding_dependencies"]:
            fail(f"checked claim still lists outstanding proof work: {claim['id']}")
        api_record = api_by_name.get(claim["lean"])
        if api_record is None or api_record.get("owner") != claim["analytic_owner"]:
            fail(f"main claim lacks its exact public API owner: {claim['id']}")
        canary = ROOT / claim["public_canary"]
        if not canary.is_file() or claim["lean"].rsplit(".", 1)[-1] not in canary.read_text():
            fail(f"main claim lacks its named public canary: {claim['id']}")
    check_lean_declarations(claims)


def main() -> None:
    contract = load(CONTRACT_PATH)
    snapshot = load(SNAPSHOT_PATH)
    results = load(RESULT_PATH).get("result", [])
    api = load(API_PATH).get("declaration", [])
    certificates = load(CERTIFICATE_PATH).get("certificate", [])
    replay_families = load(REPLAY_PATH).get("family", [])
    if contract.get("schema_version") != 2:
        fail("unsupported main-result contract schema")
    if contract.get("paper_parameters") != EXPECTED_PAPER_PARAMETERS:
        fail("paper parameter block differs from the reviewed exact constants")
    check_headline_inventory(contract, results)
    check_result_parameter_binding(contract["paper_parameters"], results)
    paper = check_snapshot(snapshot)
    check_catalog_links(contract, results, api, certificates, replay_families)
    claims = contract.get("claim", [])
    check_claim_semantic_digest(contract, claims)
    check_claims(claims, paper, api)
    check_counterexample_evidence_digest(contract)
    all_paper = "\n".join(paper.values())
    for result in results:
        if result["paper_locator"] not in all_paper:
            fail(f"advertised result has no pinned paper locator: {result['id']}")
    subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "generate_formalization_table.py"), "--check"],
        check=True,
    )
    pending = sum(result["verification_class"] == "replay_pending" for result in results)
    outstanding = sum(
        claim["verification_class"] == "proof_outstanding"
        for claim in contract.get("claim", [])
    )
    print(
        f"main-result contract verified: {len(results)} advertised results "
        f"({pending} replay pending), {len(contract.get('claim', []))} substantive claims "
        f"({outstanding} proof outstanding)"
    )


if __name__ == "__main__":
    main()
