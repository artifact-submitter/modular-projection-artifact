#!/usr/bin/env python3
"""Run a bounded, manifest-driven exact counterexample search."""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import time
import tomllib

from counterexample_catalog import ROOT
from counterexample_probability import (
    ProbabilityError, centered_residue_counts, compare_dyadic_budget,
    coordinate_lower_probability, cutoff_mass, identical_energy_convolution,
    integer_shift_residue_counts, squared_energy_distribution,
    validate_modular_instance, weighted_row_sums,
)


class SearchError(ValueError):
    pass


MAX_MANIFEST_BYTES = 4 * 1024 * 1024
MAX_DIMENSION = 4096
MAX_ROWS = 4096
MAX_CANDIDATES = 1_000_000
MAX_ENERGY_STATES = 1_000_000


def _integer(value, label: str, *, positive: bool = False) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or (positive and value <= 0):
        qualifier = "positive " if positive else ""
        raise SearchError(f"{label} must be a {qualifier}integer")
    return value


def _rational(table: dict, prefix: str) -> Fraction:
    numerator, denominator = table.get(f"{prefix}_numerator"), table.get(f"{prefix}_denominator")
    if not isinstance(numerator, str) or not numerator.lstrip("-").isdigit():
        raise SearchError(f"{prefix}_numerator must be a decimal integer string")
    if not isinstance(denominator, str) or not denominator.isdigit() or int(denominator) <= 0:
        raise SearchError(f"{prefix}_denominator must be a positive decimal integer string")
    return Fraction(int(numerator), int(denominator))


def load_manifest(path: Path) -> tuple[dict, str]:
    try:
        raw = path.read_bytes()
        if len(raw) > MAX_MANIFEST_BYTES:
            raise SearchError("search manifest exceeds the audited size bound")
        manifest = tomllib.loads(raw.decode("utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise SearchError(f"cannot load search manifest: {error}") from error
    required = {
        "schema_version", "id", "family", "rows", "public_threshold",
        "modulus", "event_comparison", "budget_bits", "constructor",
        "coefficient_class", "shift_class", "seed", "time_limit_seconds",
        "memory_limit_mb", "max_candidates", "dimension_min", "dimension_max",
        "support_abs_max", "max_energy_states", "output",
    }
    missing = sorted(required - set(manifest))
    if missing:
        raise SearchError(f"manifest lacks required fields: {missing}")
    if manifest["schema_version"] != 1 or manifest["family"] not in {"l2-lower", "linf-lower"}:
        raise SearchError("unsupported manifest schema or search family")
    if manifest["coefficient_class"] != "balanced_ternary" or manifest["shift_class"] not in {"zero_integer", "bounded_integer"}:
        raise SearchError("search requires balanced-ternary coefficients and explicit integer shifts")
    for field in ("rows", "public_threshold", "modulus", "time_limit_seconds", "memory_limit_mb", "max_candidates", "dimension_min", "dimension_max", "support_abs_max", "max_energy_states"):
        _integer(manifest[field], field, positive=True)
    if manifest["dimension_min"] > manifest["dimension_max"]:
        raise SearchError("dimension_min must not exceed dimension_max")
    if (manifest["dimension_max"] > MAX_DIMENSION or manifest["rows"] > MAX_ROWS or
        manifest["max_candidates"] > MAX_CANDIDATES or
        manifest["max_energy_states"] > MAX_ENERGY_STATES):
        raise SearchError("manifest exceeds audited dimension/row/candidate/state bounds")
    if manifest["modulus"] % 2 == 0:
        raise SearchError("finite modular searches require a positive odd modulus")
    _integer(manifest["seed"], "seed")
    _integer(manifest["budget_bits"], "budget_bits")
    output = ROOT / manifest["output"]
    search_root = (ROOT / "evidence" / "counterexamples" / "searches").resolve()
    if output.resolve().parent != search_root or output.suffix != ".json":
        raise SearchError("output must be one JSON file directly under evidence/counterexamples/searches")
    return manifest, hashlib.sha256(raw).hexdigest()


def candidates(manifest: dict):
    constructor = manifest["constructor"]
    if constructor == "explicit_vector":
        vectors = manifest.get("vectors")
        if not isinstance(vectors, list) or not vectors:
            raise SearchError("explicit_vector requires a nonempty vectors list")
        for vector in vectors:
            if not isinstance(vector, list) or not manifest["dimension_min"] <= len(vector) <= manifest["dimension_max"] or len(vector) > MAX_DIMENSION:
                raise SearchError("explicit vector dimension is outside the audited manifest bounds")
            if any(isinstance(value, bool) or not isinstance(value, int) or abs(value) > manifest["support_abs_max"] for value in vector):
                raise SearchError("explicit vector support is outside the audited manifest bounds")
            yield vector
    elif constructor == "constant_vector":
        dimensions, values = manifest.get("dimensions"), manifest.get("vector_values")
        if not isinstance(dimensions, list) or not dimensions or not isinstance(values, list) or not values:
            raise SearchError("constant_vector requires nonempty dimensions and vector_values lists")
        for dimension in dimensions:
            dimension = _integer(dimension, "dimension", positive=True)
            if not manifest["dimension_min"] <= dimension <= manifest["dimension_max"] or dimension > MAX_DIMENSION:
                raise SearchError("constant-vector dimension is outside the audited manifest bounds")
            for value in values:
                value = _integer(value, "constant vector value")
                if abs(value) > manifest["support_abs_max"]:
                    raise SearchError("constant-vector support is outside the audited manifest bounds")
                yield [value] * dimension
    elif constructor == "singleton":
        yield [manifest["public_threshold"]]
    else:
        raise SearchError(f"unsupported constructor: {constructor}")


def _accepted_energy_cutoff(cutoff: Fraction, comparison: str) -> int:
    if comparison == "strict_lt":
        return (cutoff.numerator - 1) // cutoff.denominator
    if comparison == "closed_le":
        return cutoff.numerator // cutoff.denominator
    raise SearchError("bounded lower searches require strict_lt or closed_le")


def evaluate_candidate(manifest: dict, vector: list[int], shift: int, *, deadline: float | None = None) -> dict:
    threshold, modulus, rows = manifest["public_threshold"], manifest["modulus"], manifest["rows"]
    margin = _rational(manifest, "minimum_modulus_multiplier")
    if not manifest["dimension_min"] <= len(vector) <= manifest["dimension_max"]:
        raise SearchError("candidate dimension is outside the manifest bounds")
    if any(isinstance(value, bool) or not isinstance(value, int) or abs(value) > manifest["support_abs_max"] for value in vector):
        raise SearchError("candidate support is outside the centered integer support bounds")
    _integer(shift, "integer shift")
    validate_modular_instance(
        vector, threshold, modulus, minimum_modulus_multiplier=margin,
    )
    row_support_bound = 2 * sum(abs(value) for value in vector) + 1
    if row_support_bound > manifest["max_energy_states"]:
        raise ProbabilityError("manifest state limit is below the conservative row-support bound")
    row_weight_bytes = (2 * len(vector) + 7) // 8 + 64
    final_probability_bytes = (2 * len(vector) * rows + 7) // 8 + 64
    pre_row_bytes = 4 * row_support_bound * row_weight_bytes + 4 * final_probability_bytes + 64 * len(vector)
    if pre_row_bytes > manifest["memory_limit_mb"] * 1024 * 1024:
        raise ProbabilityError("manifest memory limit is insufficient for the conservative row-distribution bound")
    base = weighted_row_sums(
        vector, deadline=deadline, state_limit=manifest["max_energy_states"]
    )
    residues = integer_shift_residue_counts(base, modulus, shift)
    denominator = sum(base.values())
    if manifest["family"] == "l2-lower":
        multiplier = _rational(manifest, "threshold_multiplier")
        if multiplier < 0:
            raise SearchError("threshold multiplier must be nonnegative")
        cutoff = multiplier * threshold * threshold
        accepted_cutoff = _accepted_energy_cutoff(cutoff, manifest["event_comparison"])
        if accepted_cutoff < 0:
            probability = Fraction(0)
            return {
                "vector": vector, "integer_shift": shift,
                "probability_numerator": "0", "probability_denominator": "1",
                "refutes_strict_budget": False,
            }
        state_bound = min(accepted_cutoff + 1, manifest["max_energy_states"])
        probability_integer_bytes = (2 * len(vector) * rows + 7) // 8 + 64
        conservative_bytes = 4 * state_bound * probability_integer_bytes + 64 * len(vector)
        if conservative_bytes > manifest["memory_limit_mb"] * 1024 * 1024:
            raise ProbabilityError("manifest memory limit is insufficient for the exact energy-state bound")
        distribution = identical_energy_convolution(
            squared_energy_distribution(residues), rows, accepted_cutoff,
            deadline=deadline, state_limit=manifest["max_energy_states"],
        )
        probability = Fraction(sum(distribution.values()), denominator**rows)
    else:
        cap = _rational(manifest, "coordinate_cap")
        if cap < 0:
            raise SearchError("coordinate cap must be nonnegative")
        bound_squared = cap * cap * threshold * threshold
        accepted = cutoff_mass(squared_energy_distribution(residues), bound_squared, manifest["event_comparison"])
        probability = coordinate_lower_probability(Fraction(accepted, denominator), rows)
    return {
        "vector": vector,
        "integer_shift": shift,
        "probability_numerator": str(probability.numerator),
        "probability_denominator": str(probability.denominator),
        "refutes_strict_budget": compare_dyadic_budget(probability, manifest["budget_bits"]),
    }


def run_search(manifest: dict, manifest_sha256: str) -> dict:
    start = time.monotonic()
    deadline = start + manifest["time_limit_seconds"]
    shifts = manifest.get("integer_shifts", [0])
    if manifest["shift_class"] == "zero_integer" and shifts != [0]:
        raise SearchError("zero_integer shift class must enumerate exactly [0]")
    if not shifts or any(isinstance(x, bool) or not isinstance(x, int) for x in shifts):
        raise SearchError("integer_shifts must be a nonempty integer list")
    if len(shifts) > MAX_CANDIDATES:
        raise SearchError("integer shift enumeration exceeds the audited candidate bound")
    best = None
    examined = 0
    uncovered = None
    constructor = manifest["constructor"]
    if constructor == "explicit_vector":
        vector_count = len(manifest.get("vectors", []))
    elif constructor == "constant_vector":
        vector_count = len(manifest.get("dimensions", [])) * len(manifest.get("vector_values", []))
    elif constructor == "singleton":
        vector_count = 1
    else:
        raise SearchError(f"unsupported constructor: {constructor}")
    total = vector_count * len(shifts)
    if total <= 0:
        raise SearchError("manifest candidate domain must be nonempty")
    if total > MAX_CANDIDATES:
        raise SearchError("manifest candidate product exceeds the audited bound")
    stopped = False
    for vector in candidates(manifest):
        for shift in shifts:
            if examined >= manifest["max_candidates"] or time.monotonic() > deadline:
                uncovered = {
                    "reason": "candidate_or_time_limit",
                    "first_unexamined": {"vector": vector, "integer_shift": shift},
                    "remaining_candidates": total - examined,
                }
                stopped = True
                break
            examined += 1
            try:
                result = evaluate_candidate(manifest, vector, shift, deadline=deadline)
            except ProbabilityError as error:
                if not any(token in str(error) for token in ("deadline", "state limit", "memory limit")):
                    raise
                uncovered = {
                    "reason": "time_memory_or_energy_state_limit",
                    "first_unfinished": {"vector": vector, "integer_shift": shift},
                    "remaining_candidates": total - examined + 1,
                }
                stopped = True
                break
            if best is None:
                best = result
            else:
                left = int(result["probability_numerator"]) * int(best["probability_denominator"])
                right = int(best["probability_numerator"]) * int(result["probability_denominator"])
                if left > right:
                    best = result
        if stopped:
            break
    return {
        "schema_version": 1,
        "manifest_id": manifest["id"],
        "manifest_sha256": manifest_sha256,
        "family": manifest["family"],
        "deterministic_seed": manifest["seed"],
        "candidates_total": total,
        "candidates_examined": examined,
        "search_complete": uncovered is None and examined == total,
        "optimum_claimed": False,
        "best_exact_witness": best,
        "uncovered_domain": uncovered,
        "resource_exhaustion_is_negative_result": False,
    }


def serialized(result: dict) -> str:
    return json.dumps(result, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--check", action="store_true", help="compare with retained output")
    args = parser.parse_args()
    try:
        manifest, digest = load_manifest(args.manifest)
        content = serialized(run_search(manifest, digest))
        output = ROOT / manifest["output"]
        if args.check:
            if not output.is_file() or output.read_text(encoding="utf-8") != content:
                raise SearchError(f"retained search output is stale: {output.relative_to(ROOT)}")
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(content, encoding="utf-8")
    except (SearchError, ProbabilityError) as error:
        print(f"counterexample search error: {error}", file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
