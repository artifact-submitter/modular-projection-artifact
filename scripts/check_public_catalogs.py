#!/usr/bin/env python3
"""Validate the timeless result and intentional public-API catalogs."""

from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import re
import sys
import tomllib

from lean_source import LeanSourceError, qualified_declarations


ROOT = Path(__file__).resolve().parents[1]
RESULT_PATH = ROOT / "evidence" / "result-catalog.toml"
API_PATH = ROOT / "evidence" / "public-api.toml"
SOURCE_PATH = ROOT / "evidence" / "source-correspondence.toml"
ALLOWED_VERIFICATION_CLASSES = {
    "replay_pending",
    "kernel_checked",
    "native_attested",
    "explicit_assumption_reduction",
    "external_exact_artifact",
    "not_formalized",
}
REQUIRED_RESULT_FIELDS = {
    "id",
    "row_law",
    "statistic",
    "tail",
    "rows",
    "input_condition",
    "failure_budget",
    "event_comparison",
    "probability_comparison",
    "lean",
    "lean_owner",
    "verification_class",
    "certificate_ids",
    "paper_locator",
    "paper_scope_tex",
}
FORBIDDEN_HISTORY_WORDS = {"phase", "scaffolded", "superseded"}


def fail(message: str) -> None:
    print(f"public catalog error: {message}", file=sys.stderr)
    raise SystemExit(1)


def load(path: Path) -> dict:
    with path.open("rb") as source:
        return tomllib.load(source)


def require_unique(records: list[dict], field: str, label: str) -> None:
    values = [record.get(field) for record in records]
    missing = [index for index, value in enumerate(values) if not value]
    if missing:
        fail(f"{label} records {missing} have no {field}")
    duplicates = sorted(
        value for value in set(values) if values.count(value) > 1
    )
    if duplicates:
        fail(f"duplicate {label} {field}: {duplicates}")


def source_declarations(owners: set[str]) -> dict[str, set[str]]:
    declarations: dict[str, set[str]] = {}
    for owner in sorted(owners):
        path = ROOT / owner
        if not path.is_file():
            fail(f"cataloged Lean owner does not exist: {owner}")
        try:
            declarations[owner] = qualified_declarations(
                path.read_text(encoding="utf-8"), owner
            )
        except LeanSourceError as error:
            fail(str(error))
    return declarations


def check_no_history(record: dict, label: str) -> None:
    rendered = " ".join(str(value).lower() for value in record.values())
    found = sorted(word for word in FORBIDDEN_HISTORY_WORDS if word in rendered)
    if found:
        fail(f"{label} contains development-history vocabulary: {found}")


def main() -> None:
    results_doc = load(RESULT_PATH)
    api_doc = load(API_PATH)
    source_doc = load(SOURCE_PATH)
    if results_doc.get("schema_version") != 1:
        fail("unsupported result catalog schema")
    if api_doc.get("schema_version") != 1:
        fail("unsupported public API schema")
    if source_doc.get("schema_version") != 1:
        fail("unsupported source-correspondence schema")

    results = results_doc.get("result", [])
    api = api_doc.get("declaration", [])
    if not results:
        fail("result catalog is empty")
    if not api:
        fail("public API catalog is empty")
    require_unique(results, "id", "result")
    require_unique(results, "lean", "result")
    require_unique(api, "name", "public API")
    sources = source_doc.get("source", [])
    require_unique(sources, "id", "source correspondence")
    result_ids = {result["id"] for result in results}
    for source in sources:
        required = {"id", "title", "locator", "scope", "result_ids"}
        missing = sorted(required - set(source))
        if missing:
            fail(f"source correspondence {source.get('id')} misses fields: {missing}")
        unknown = sorted(set(source["result_ids"]) - result_ids)
        if unknown:
            fail(f"source correspondence {source['id']} has unknown results: {unknown}")

    for result in results:
        missing = sorted(REQUIRED_RESULT_FIELDS - set(result))
        if missing:
            fail(f"result {result.get('id')} misses fields: {missing}")
        if re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", result["id"]) is None:
            fail(f"invalid stable result ID: {result['id']}")
        if result["verification_class"] not in ALLOWED_VERIFICATION_CLASSES:
            fail(
                f"invalid verification class for {result['id']}: "
                f"{result['verification_class']}"
            )
        if result["event_comparison"] not in {
            "strict_lt",
            "strict_gt",
            "closed_le",
            "closed_ge",
        }:
            fail(f"invalid event comparison for {result['id']}")
        if result["probability_comparison"] != "strict_lt":
            fail(f"public failure probability is not strict: {result['id']}")
        if not isinstance(result["certificate_ids"], list):
            fail(f"certificate_ids is not a list: {result['id']}")
        if result["statistic"] == "modular_l2_squared":
            cap_kind = result.get("input_norm_cap_kind")
            if result["tail"] == "upper":
                if cap_kind != "unrestricted":
                    fail(f"modular L2 upper result has an input cap: {result['id']}")
            elif result["tail"] == "lower":
                if cap_kind not in {
                    "l2_over_modulus",
                    "public_threshold_over_modulus",
                }:
                    fail(
                        "modular L2 lower result has no structured input condition: "
                        f"{result['id']}"
                    )
                if cap_kind == "l2_over_modulus":
                    numerator = result.get("input_norm_cap_numerator")
                    denominator = result.get("input_norm_cap_denominator")
                else:
                    if result.get("input_threshold_relation") != "b^2 <= sqNorm(w)":
                        fail(f"invalid threshold/norm relation: {result['id']}")
                    numerator = result.get("modulus_margin_numerator")
                    denominator = result.get("modulus_margin_denominator")
                if not isinstance(numerator, int) or numerator < 0:
                    fail(f"invalid input-condition numerator: {result['id']}")
                if not isinstance(denominator, int) or denominator <= 0:
                    fail(f"invalid input-condition denominator: {result['id']}")
            else:
                fail(f"invalid modular L2 tail: {result['id']}")
        check_no_history(result, f"result {result['id']}")

    owners = {
        record["lean_owner"] for record in results
    } | {record.get("owner", "") for record in api}
    if "" in owners:
        fail("every public API declaration must name its owner")
    declarations = source_declarations(owners)

    for result in results:
        if result["lean"] not in declarations[result["lean_owner"]]:
            fail(
                f"result declaration {result['lean']} is absent from "
                f"{result['lean_owner']}"
            )
    for record in api:
        required = {"name", "kind", "owner"}
        missing = sorted(required - set(record))
        if missing:
            fail(f"public API record misses fields: {missing}")
        check_no_history(record, f"public API declaration {record['name']}")
        if record["name"] not in declarations[record["owner"]]:
            fail(
                f"public API declaration {record['name']} is absent from "
                f"{record['owner']}"
            )

    api_names = {record["name"] for record in api}
    missing_results = sorted(
        result["lean"] for result in results if result["lean"] not in api_names
    )
    if missing_results:
        fail(f"certified results absent from public API: {missing_results}")

    by_axis: dict[tuple[str, str, str], int] = defaultdict(int)
    for result in results:
        by_axis[(result["row_law"], result["statistic"], result["tail"])] += 1
    print(
        f"public catalogs verified: {len(results)} results, "
        f"{len(api)} supported declarations, {len(by_axis)} axis classes"
    )


if __name__ == "__main__":
    main()
