#!/usr/bin/env python3
"""Parsing and normalization for structured counterexample evidence."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tomllib
from typing import Iterable, Mapping


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence" / "counterexamples"
FAMILY_IDS = {
    "l2-lower", "masked-l2-lower", "linf-lower",
    "masked-linf-lower", "l2-upper", "linf-upper",
}
TRUST_ORDER = {
    "proof_outstanding": 0,
    "external_exact_artifact": 1,
    "replay_pending": 2,
    "native_attested": 3,
    "kernel_checked": 4,
}


class CatalogError(ValueError):
    """An explicit, user-facing counterexample catalog failure."""


@dataclass(frozen=True)
class Catalogs:
    families: dict
    witnesses: dict
    comparisons: dict
    results: dict
    contract: dict


def load_toml(path: Path) -> dict:
    try:
        with path.open("rb") as source:
            return tomllib.load(source)
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise CatalogError(f"cannot load {path}: {error}") from error


def load_catalogs(root: Path = ROOT) -> Catalogs:
    base = root / "evidence" / "counterexamples"
    return Catalogs(
        load_toml(base / "families.toml"),
        load_toml(base / "witnesses.toml"),
        load_toml(base / "comparisons.toml"),
        load_toml(root / "evidence" / "result-catalog.toml"),
        load_toml(root / "evidence" / "theorem-contract.toml"),
    )


def require_unique(records: Iterable[Mapping], field: str, label: str) -> dict[str, Mapping]:
    indexed: dict[str, Mapping] = {}
    for record in records:
        value = record.get(field)
        if not isinstance(value, str) or not value:
            raise CatalogError(f"every {label} must have a nonempty {field}")
        if value in indexed:
            raise CatalogError(f"duplicate {label} {field}: {value}")
        indexed[value] = record
    return indexed


def rational(record: Mapping, prefix: str) -> Fraction:
    numerator = record.get(f"{prefix}_numerator")
    denominator = record.get(f"{prefix}_denominator")
    if not isinstance(numerator, str) or not numerator or not numerator.lstrip("-").isdigit():
        raise CatalogError(f"{prefix}_numerator must be a decimal integer string")
    if not isinstance(denominator, str) or not denominator.isdigit() or int(denominator) <= 0:
        raise CatalogError(f"{prefix}_denominator must be a positive decimal integer string")
    return Fraction(int(numerator), int(denominator))


def semantic_digest(records: Iterable[Mapping]) -> str:
    payload = json.dumps(
        sorted(records, key=lambda record: record["id"]),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def record_digest(record: Mapping) -> str:
    payload = json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def source_digests(results: list[dict], claims: list[dict]) -> tuple[str, str]:
    return semantic_digest(results), semantic_digest(claims)


def family_for_result(result: Mapping) -> str:
    statistic, tail = result.get("statistic"), result.get("tail")
    if tail == "upper":
        if statistic in {"modular_l2_squared", "affine_modular_l2_norm"}:
            return "l2-upper"
        if statistic in {"modular_linf", "affine_modular_linf"}:
            return "linf-upper"
    elif tail == "lower":
        return {
            "modular_l2_squared": "l2-lower",
            "affine_modular_l2_squared": "masked-l2-lower",
            "modular_linf": "linf-lower",
            "affine_modular_linf": "masked-linf-lower",
        }.get(statistic, "")
    raise CatalogError(f"unsupported result semantics: statistic={statistic!r}, tail={tail!r}")


def result_threshold(result: Mapping) -> Fraction:
    for prefix in ("threshold", "coordinate_threshold", "coordinate_cap"):
        numerator = result.get(f"{prefix}_numerator")
        denominator = result.get(f"{prefix}_denominator")
        if numerator is not None or denominator is not None:
            if isinstance(numerator, bool) or not isinstance(numerator, int):
                raise CatalogError(f"invalid {prefix} numerator in {result.get('id')}")
            if isinstance(denominator, bool) or not isinstance(denominator, int) or denominator <= 0:
                raise CatalogError(f"invalid {prefix} denominator in {result.get('id')}")
            return Fraction(numerator, denominator)
    raise CatalogError(f"result has no threshold: {result.get('id')}")


def result_unit_key(result: Mapping) -> tuple:
    """Identify one optimization unit while preserving source event semantics."""
    threshold = result_threshold(result)
    return (
        family_for_result(result),
        result.get("rows"),
        result.get("failure_budget"),
        threshold.numerator,
        threshold.denominator,
        result.get("modulus_margin_numerator"),
        result.get("modulus_margin_denominator"),
    )


def trust_min(classes: Iterable[str]) -> str:
    values = list(classes)
    if not values:
        raise CatalogError("cannot derive trust from no dependencies")
    unknown = sorted(set(values) - TRUST_ORDER.keys())
    if unknown:
        raise CatalogError(f"unknown verification classes: {unknown}")
    return min(values, key=TRUST_ORDER.__getitem__)


def canonical_unit_id(key: tuple) -> str:
    family, rows, budget, num, den, margin_num, margin_den = key
    threshold = str(num) if den == 1 else f"{num}-over-{den}"
    budget_slug = str(budget).replace("^-", "").replace("^", "").replace("-", "")
    margin = "unrestricted" if margin_num is None else f"margin-{margin_num}-over-{margin_den}"
    return f"{family}-rows{rows}-{threshold}-{budget_slug}-{margin}"
