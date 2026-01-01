#!/usr/bin/env python3
"""Small exact operations for finite counterexample searches and validation.

All probabilities are :class:`fractions.Fraction` values.  The functions in
this module deliberately accept structured data rather than expressions read
from an evidence file.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
import time
from typing import Iterable, Mapping, Sequence


class ProbabilityError(ValueError):
    """Raised when an exact probability input is malformed or inadmissible."""


def _require_integer(value: object, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ProbabilityError(f"{label} must be an integer")
    return value


def weighted_row_sums(
    vector: Sequence[int],
    coefficient_weights: Mapping[int, int] | None = None,
    *,
    deadline: float | None = None,
    state_limit: int | None = None,
) -> Counter[int]:
    """Return the exact weighted distribution of a row dot product.

    Balanced ternary uses the four-symbol weights ``{-1: 1, 0: 2, 1: 1}``.
    The duplicate zero symbol is represented by its weight, not by sampling.
    """
    weights = {-1: 1, 0: 2, 1: 1} if coefficient_weights is None else coefficient_weights
    if not vector:
        raise ProbabilityError("vector must be nonempty")
    if not weights:
        raise ProbabilityError("coefficient weights must be nonempty")
    checked_vector = [_require_integer(x, "vector coefficient") for x in vector]
    checked_weights: dict[int, int] = {}
    for coefficient, weight in weights.items():
        coefficient = _require_integer(coefficient, "row coefficient")
        weight = _require_integer(weight, "row coefficient weight")
        if weight <= 0:
            raise ProbabilityError("row coefficient weights must be positive")
        checked_weights[coefficient] = weight
    counts: Counter[int] = Counter({0: 1})
    for value in checked_vector:
        if deadline is not None and time.monotonic() > deadline:
            raise ProbabilityError("weighted row sums exceeded their deadline")
        out: Counter[int] = Counter()
        operations = 0
        for partial, multiplicity in counts.items():
            for coefficient, weight in checked_weights.items():
                operations += 1
                if deadline is not None and operations % 1024 == 0 and time.monotonic() > deadline:
                    raise ProbabilityError("weighted row sums exceeded their deadline")
                out[partial + coefficient * value] += multiplicity * weight
        counts = out
        if state_limit is not None:
            state_limit = _require_integer(state_limit, "state limit")
            if state_limit <= 0 or len(counts) > state_limit:
                raise ProbabilityError("weighted row sums exceeded their support-state limit")
    return counts


def centered_residue(value: int, modulus: int) -> int:
    """Return the canonical centered residue for a positive odd modulus."""
    value = _require_integer(value, "value")
    modulus = _require_integer(modulus, "modulus")
    if modulus <= 0 or modulus % 2 == 0:
        raise ProbabilityError("modulus must be a positive odd integer")
    residue = value % modulus
    return residue - modulus if residue > modulus // 2 else residue


def centered_residue_counts(
    counts: Mapping[int, int], modulus: int
) -> Counter[int]:
    out: Counter[int] = Counter()
    for value, weight in counts.items():
        value = _require_integer(value, "support value")
        weight = _require_integer(weight, "support weight")
        if weight < 0:
            raise ProbabilityError("support weights must be nonnegative")
        out[centered_residue(value, modulus)] += weight
    return out


def integer_shift_residue_counts(
    counts: Mapping[int, int], modulus: int, shift: int
) -> Counter[int]:
    """Center after adding an admissible integer mask coordinate."""
    shift = _require_integer(shift, "mask shift")
    checked: dict[int, int] = {}
    for value, weight in counts.items():
        value = _require_integer(value, "support value")
        weight = _require_integer(weight, "support weight")
        if weight < 0:
            raise ProbabilityError("support weights must be nonnegative")
        checked[value + shift] = checked.get(value + shift, 0) + weight
    return centered_residue_counts(checked, modulus)


def squared_energy_distribution(counts: Mapping[int, int]) -> Counter[int]:
    out: Counter[int] = Counter()
    for value, weight in counts.items():
        value = _require_integer(value, "support value")
        weight = _require_integer(weight, "support weight")
        if weight < 0:
            raise ProbabilityError("support weights must be nonnegative")
        out[value * value] += weight
    return out


def convolve_energy_rows(
    rows: Iterable[Mapping[int, int]],
    cutoff: int | None = None,
    *,
    deadline: float | None = None,
    state_limit: int | None = None,
) -> Counter[int]:
    """Convolve heterogeneous nonnegative energy distributions exactly.

    If ``cutoff`` is supplied, larger partial sums are discarded.  This is
    sound only because every accepted energy key is checked nonnegative.
    """
    if cutoff is not None:
        cutoff = _require_integer(cutoff, "cutoff")
        if cutoff < 0:
            raise ProbabilityError("cutoff must be nonnegative")
    total: Counter[int] = Counter({0: 1})
    used = False
    for row in rows:
        if deadline is not None and time.monotonic() > deadline:
            raise ProbabilityError("exact convolution exceeded its deadline")
        used = True
        checked: dict[int, int] = {}
        for energy, weight in row.items():
            energy = _require_integer(energy, "energy")
            weight = _require_integer(weight, "energy weight")
            if energy < 0:
                raise ProbabilityError("energies must be nonnegative")
            if weight < 0:
                raise ProbabilityError("energy weights must be nonnegative")
            checked[energy] = checked.get(energy, 0) + weight
        if not checked or sum(checked.values()) <= 0:
            raise ProbabilityError("each row distribution must have positive total mass")
        out: Counter[int] = Counter()
        operations = 0
        for partial, left_weight in total.items():
            for energy, right_weight in checked.items():
                operations += 1
                if deadline is not None and operations % 1024 == 0 and time.monotonic() > deadline:
                    raise ProbabilityError("exact convolution exceeded its deadline")
                combined = partial + energy
                if cutoff is None or combined <= cutoff:
                    out[combined] += left_weight * right_weight
        total = out
        if state_limit is not None:
            state_limit = _require_integer(state_limit, "state limit")
            if state_limit <= 0 or len(total) > state_limit:
                raise ProbabilityError("exact convolution exceeded its energy-state limit")
    if not used:
        raise ProbabilityError("at least one row distribution is required")
    return total


def identical_energy_convolution(
    row: Mapping[int, int], rows: int, cutoff: int | None = None, *,
    deadline: float | None = None, state_limit: int | None = None,
) -> Counter[int]:
    rows = _require_integer(rows, "row count")
    if rows <= 0:
        raise ProbabilityError("row count must be positive")
    return convolve_energy_rows(
        (row for _ in range(rows)), cutoff, deadline=deadline, state_limit=state_limit
    )


def _exact_fraction(value: object, label: str) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise ProbabilityError(f"{label} must be an integer or Fraction")
    return Fraction(value)


def cutoff_mass(
    distribution: Mapping[int, int], cutoff: Fraction | int, comparison: str
) -> int:
    """Evaluate an exact strict/closed cutoff without floating point."""
    cutoff = _exact_fraction(cutoff, "cutoff")
    predicates = {
        "strict_lt": lambda value: Fraction(value) < cutoff,
        "closed_le": lambda value: Fraction(value) <= cutoff,
        "strict_gt": lambda value: Fraction(value) > cutoff,
        "closed_ge": lambda value: Fraction(value) >= cutoff,
    }
    if comparison not in predicates:
        raise ProbabilityError(f"unknown cutoff comparison: {comparison}")
    total = 0
    for value, weight in distribution.items():
        value = _require_integer(value, "support value")
        weight = _require_integer(weight, "support weight")
        if weight < 0:
            raise ProbabilityError("support weights must be nonnegative")
        if predicates[comparison](value):
            total += weight
    return total


def coordinate_lower_probability(row_acceptance: Fraction, rows: int) -> Fraction:
    rows = _require_integer(rows, "row count")
    probability = _exact_fraction(row_acceptance, "row probability")
    if rows <= 0 or probability < 0 or probability > 1:
        raise ProbabilityError("invalid row count or probability")
    return probability**rows


def coordinate_upper_probability(row_failure: Fraction, rows: int) -> Fraction:
    rows = _require_integer(rows, "row count")
    probability = _exact_fraction(row_failure, "row probability")
    if rows <= 0 or probability < 0 or probability > 1:
        raise ProbabilityError("invalid row count or probability")
    return 1 - (1 - probability) ** rows


def compare_dyadic_budget(probability: Fraction, bits: int, guarantee: str = "strict_lt") -> bool:
    """Return whether ``probability`` refutes a dyadic theorem guarantee.

    A theorem claiming ``Pr[event] < 2^-bits`` is refuted at equality as well.
    """
    bits = _require_integer(bits, "security bits")
    probability = _exact_fraction(probability, "probability")
    if bits < 0 or probability < 0 or probability > 1:
        raise ProbabilityError("invalid security bits or probability")
    scaled_left = probability.numerator * (1 << bits)
    if guarantee == "strict_lt":
        return scaled_left >= probability.denominator
    if guarantee == "closed_le":
        return scaled_left > probability.denominator
    raise ProbabilityError(f"unknown probability guarantee: {guarantee}")


def validate_modular_instance(
    vector: Sequence[int],
    threshold: int,
    modulus: int,
    mask: Sequence[int] | None = None,
    *,
    mask_rows: int | None = None,
    minimum_modulus_multiplier: Fraction | int | None = None,
    require_threshold_norm: bool = True,
) -> None:
    """Reject inputs outside the finite modular search domain."""
    threshold = _require_integer(threshold, "public threshold")
    modulus = _require_integer(modulus, "modulus")
    if threshold <= 0:
        raise ProbabilityError("public threshold must be a positive integer")
    if modulus <= 0 or modulus % 2 == 0:
        raise ProbabilityError("modulus must be a positive odd integer")
    if not vector:
        raise ProbabilityError("vector must be nonempty")
    radius = modulus // 2
    norm_squared = 0
    for value in vector:
        value = _require_integer(value, "vector coefficient")
        if not -radius <= value <= radius:
            raise ProbabilityError("input vector is not centered modulo q")
        norm_squared += value * value
    if require_threshold_norm and threshold * threshold > norm_squared:
        raise ProbabilityError("public threshold does not satisfy b^2 <= sqNorm(vector)")
    if mask is not None:
        for value in mask:
            _require_integer(value, "mask coordinate")
        if mask_rows is not None:
            mask_rows = _require_integer(mask_rows, "mask row count")
            if mask_rows <= 0 or len(mask) != mask_rows:
                raise ProbabilityError("mask length does not match the positive row count")
    elif mask_rows is not None:
        raise ProbabilityError("mask row count was supplied without a mask")
    if minimum_modulus_multiplier is not None:
        multiplier = _exact_fraction(minimum_modulus_multiplier, "modulus multiplier")
        if multiplier <= 0 or Fraction(modulus, threshold) < multiplier:
            raise ProbabilityError("modulus does not meet the required rational margin")


def require_no_wrap(vector: Sequence[int], modulus: int, max_abs_coefficient: int = 1) -> None:
    """Check a sufficient no-wrap condition for bounded row coefficients."""
    modulus = _require_integer(modulus, "modulus")
    max_abs_coefficient = _require_integer(max_abs_coefficient, "coefficient bound")
    if modulus <= 0 or modulus % 2 == 0:
        raise ProbabilityError("modulus must be a positive odd integer")
    if not vector:
        raise ProbabilityError("vector must be nonempty")
    if max_abs_coefficient < 0:
        raise ProbabilityError("coefficient bound must be nonnegative")
    bound = sum(abs(_require_integer(x, "vector coefficient")) for x in vector)
    if max_abs_coefficient * bound > modulus // 2:
        raise ProbabilityError("modulus is insufficient for the claimed no-wrap computation")
