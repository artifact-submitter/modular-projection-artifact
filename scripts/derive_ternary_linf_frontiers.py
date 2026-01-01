#!/usr/bin/env python3
"""Search and exactly verify the two-decimal ternary L-infinity frontiers.

The floating-point LP is only a certificate generator.  ``--write`` freezes
its output to decimal rationals, adds an explicit constant slack, and records
adaptive Bernstein trees.  ``--verify`` uses only Python's standard library
and checks every rational inequality from the frozen artifact.

The Lean development must embed the resulting rational data; it must not read
the JSON artifact during elaboration.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json
import math
from math import comb, factorial
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ARTIFACT = (
    ROOT / "evidence/certificates/ternary-linf-two-decimal-frontiers.json"
)
DEFAULT_LEAN_ROOT = (
    ROOT / "CertifiedJL/Certificates/Families/LInfLower/TwoDecimal"
)

PI_LOWER = Q(3141592, 1_000_000)  # Real.pi_gt_d6
PI_UPPER = Q(3141593, 1_000_000)  # Real.pi_lt_d6
PHI1 = Q(5401, 10000)
PHI2 = Q(851, 10000)
TAIL_MOMENT_NUMERATOR = Q(97154081, 160000)
ENDPOINT_DENOMINATOR = 100_000_000


@dataclass(frozen=True)
class Case:
    name: str
    cap: Q
    split: Q
    degree: int
    diffuse_moment: Q
    slack: Q
    row_bound: Q
    rows_bits: tuple[tuple[int, int], ...]
    tail_kind: str
    tail_threshold: Q
    tail_denominator: Q


CASES = (
    Case(
        "cap24",
        Q(6, 25),
        Q(113, 250),
        20,
        Q(333, 2500),
        Q(1, 10000),
        Q(2933, 5000),
        ((256, 197),),
        "eighth_moment",
        Q(389, 50),
        Q(287, 10000),
    ),
    Case(
        "cap34",
        Q(17, 50),
        Q(111, 250),
        73,
        Q(71447, 500000),
        Q(1, 50000),
        Q(627, 1000),
        ((192, 129),),
        "eighth_moment",
        Q(36567, 5000),
        Q(367039, 10000000),
    ),
    Case(
        "cap42",
        Q(21, 50),
        Q(929, 2000),
        73,
        Q(119, 1000),
        Q(1, 50000),
        Q(13939, 20000),
        ((256, 133), (384, 200), (512, 266)),
        "degree_ten",
        Q(6),
        Q(11180),
    ),
    Case(
        "cap47",
        Q(47, 100),
        Q(4679, 10000),
        57,
        Q(2881, 25000),
        Q(1, 50000),
        Q(37831, 50000),
        ((512, 206),),
        "degree_ten",
        Q(55589, 10000),
        Q(9460),
    ),
)


def qtext(x: Q) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def lean_q(x: Q, lean_type: str = "ℝ") -> str:
    """Render an exact rational as a parenthesized Lean literal."""
    if x.denominator == 1:
        return f"({x.numerator} : {lean_type})"
    return f"({x.numerator} / {x.denominator} : {lean_type})"


def lean_list(
    values: list[Q], indent: str = "    ", lean_type: str = "ℝ"
) -> str:
    lines = []
    for start in range(0, len(values), 3):
        lines.append(
            indent
            + ", ".join(lean_q(x, lean_type) for x in values[start : start + 3])
        )
    return "[\n" + ",\n".join(lines) + "\n  ]"


def common_integer_scale(values: list[Q]) -> tuple[list[int], int]:
    """Represent rationals as integer numerators over one positive denominator."""
    denominator = math.lcm(*(value.denominator for value in values))
    numerators = [
        value.numerator * (denominator // value.denominator) for value in values
    ]
    return numerators, denominator


def lean_integer_list(values: list[int], indent: str = "    ") -> str:
    return lean_list([Q(value) for value in values], indent=indent, lean_type="ℤ")


def lean_cast_q(x: Q) -> str:
    """Render the real cast of an exact rational Lean literal."""
    return f"(({lean_q(x, 'ℚ')}) : ℝ)"


def parse_q(x: str) -> Q:
    return Q(x)


def poly_add(a: list[Q], b: list[Q]) -> list[Q]:
    out = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return trim(out)


def poly_scale(a: list[Q], c: Q) -> list[Q]:
    return trim([c * x for x in a])


def poly_mul(a: list[Q], b: list[Q]) -> list[Q]:
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def trim(a: list[Q]) -> list[Q]:
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def compose_interval(p: list[Q], a: Q, b: Q) -> list[Q]:
    out = [Q(0)]
    linear = [a, b - a]
    power = [Q(1)]
    for coefficient in p:
        out = poly_add(out, poly_scale(power, coefficient))
        power = poly_mul(power, linear)
    return out


def chebyshevs(n: int) -> list[list[Q]]:
    if n == 0:
        return [[Q(1)]]
    result = [[Q(1)], [Q(0), Q(1)]]
    for _ in range(2, n + 1):
        result.append(
            poly_add(
                poly_scale(poly_mul([Q(0), Q(1)], result[-1]), Q(2)),
                poly_scale(result[-2], Q(-1)),
            )
        )
    return result


def trig_to_power(coefficients: list[Q]) -> list[Q]:
    out = [Q(0)]
    for coefficient, polynomial in zip(
        coefficients, chebyshevs(len(coefficients) - 1), strict=True
    ):
        out = poly_add(out, poly_scale(polynomial, coefficient))
    return out


def power_to_bernstein(p: list[Q], a: Q, b: Q) -> list[Q]:
    degree = len(p) - 1
    q = compose_interval(p, a, b)
    q += [Q(0)] * (degree + 1 - len(q))
    return [
        sum(q[j] * Q(comb(i, j), comb(degree, j)) for j in range(i + 1))
        for i in range(degree + 1)
    ]


def integer_bernstein(
    p: list[Q], a: Q, b: Q, coefficient_scale: int = 1_000_000_000_000
) -> tuple[list[int], int, int, int, int]:
    """Return one common-denominator integer Bernstein vector.

    The return value is ``(numerators, denominator, a_num, b_num, interval_den)``.
    This representation makes every later de Casteljau split integer-only.
    """
    degree = len(p) - 1
    scaled = []
    for coefficient in p:
        value = coefficient * coefficient_scale
        assert value.denominator == 1
        scaled.append(value.numerator)
    interval_den = math.lcm(a.denominator, b.denominator)
    a_num = a.numerator * (interval_den // a.denominator)
    b_num = b.numerator * (interval_den // b.denominator)
    power_numerators = []
    for j in range(degree + 1):
        power_numerators.append(
            sum(
                scaled[k]
                * comb(k, j)
                * a_num ** (k - j)
                * (b_num - a_num) ** j
                * interval_den ** (degree - k)
                for k in range(j, degree + 1)
            )
        )
    choose_lcm = math.lcm(*(comb(degree, j) for j in range(degree + 1)))
    numerators = [
        sum(
            power_numerators[j]
            * comb(i, j)
            * (choose_lcm // comb(degree, j))
            for j in range(i + 1)
        )
        for i in range(degree + 1)
    ]
    denominator = coefficient_scale * interval_den**degree * choose_lcm
    exact = power_to_bernstein(p, a, b)
    assert all(Q(x, denominator) == y for x, y in zip(numerators, exact, strict=True))
    return numerators, denominator, a_num, b_num, interval_den


def split_integer_bernstein(coefficients: list[int]) -> tuple[list[int], list[int]]:
    degree = len(coefficients) - 1
    left = [
        sum(comb(i, j) * coefficients[j] * 2 ** (degree - i) for j in range(i + 1))
        for i in range(degree + 1)
    ]
    right = [
        sum(
            comb(degree - i, k) * coefficients[i + k] * 2**i
            for k in range(degree - i + 1)
        )
        for i in range(degree + 1)
    ]
    return left, right


def descend_integer(coefficients: list[int], path: str) -> list[int]:
    current = coefficients
    for step in path:
        left, right = split_integer_bernstein(current)
        current = left if step == "0" else right
    return current


def split_bernstein(coefficients: list[Q]) -> tuple[list[Q], list[Q]]:
    levels = [coefficients]
    while len(levels[-1]) > 1:
        old = levels[-1]
        levels.append([(old[i] + old[i + 1]) / 2 for i in range(len(old) - 1)])
    degree = len(coefficients) - 1
    left = [levels[row][0] for row in range(degree + 1)]
    right = [levels[degree - j][j] for j in range(degree + 1)]
    return left, right


def descend(coefficients: list[Q], path: str) -> list[Q]:
    current = coefficients
    for step in path:
        left, right = split_bernstein(current)
        current = left if step == "0" else right
    return current


def adaptive_paths(coefficients: list[Q], max_depth: int = 20) -> list[str]:
    leaves: list[str] = []

    def visit(current: list[Q], path: str) -> None:
        if min(current) >= 0:
            leaves.append(path)
            return
        if len(path) >= max_depth:
            raise RuntimeError(f"Bernstein certificate failed at {path}")
        left, right = split_bernstein(current)
        visit(left, path + "0")
        visit(right, path + "1")

    visit(coefficients, "")
    return leaves


def paths_form_full_tree(paths: Iterable[str]) -> bool:
    leaf_list = list(paths)
    leaves = set(leaf_list)
    if len(leaves) != len(leaf_list):
        return False
    if not leaves:
        return False
    if any(p != q and q.startswith(p) for p in leaves for q in leaves):
        return False

    prefixes = {leaf[:i] for leaf in leaves for i in range(len(leaf) + 1)}

    def complete(prefix: str) -> bool:
        if prefix in leaves:
            return True
        if prefix not in prefixes:
            return False
        return complete(prefix + "0") and complete(prefix + "1")

    return complete("")


def floor_to_denominator(x: Q, denominator: int) -> Q:
    return Q((x.numerator * denominator) // x.denominator, denominator)


def central_cos_taylor(cap: Q) -> Q:
    x2 = 2 * Q(111, 100) ** 2 * cap**2
    return 1 - x2 / 2 + x2**2 / 24 - x2**3 / 720


def diffuse_cos_taylor(cap: Q) -> Q:
    x = PI_UPPER * cap
    return (
        1
        - x**2 / 2
        + x**4 / 24
        - x**6 / 720
        + x**8 / 40320
        - x**10 / 3628800
    )


def central_cos_endpoint(cap: Q) -> Q:
    return floor_to_denominator(central_cos_taylor(cap), ENDPOINT_DENOMINATOR)


def diffuse_cos_endpoint(cap: Q) -> Q:
    return floor_to_denominator(diffuse_cos_taylor(cap), ENDPOINT_DENOMINATOR)


def exp_lower_sum(x: Q, terms: int) -> Q:
    return sum(x**k / factorial(k) for k in range(terms + 1))


def first_exp_terms(x: Q, inverse_target: Q) -> int:
    for terms in range(1, 80):
        if exp_lower_sum(x, terms) > inverse_target:
            return terms
    raise RuntimeError("Taylor lower sum did not close")


def tail_polynomial() -> list[Q]:
    # X (X - 139/100)^2 ((X - 61/4)^2 + 4)
    return poly_mul(
        [Q(0), Q(1)],
        poly_mul(
            poly_mul([Q(-139, 100), Q(1)], [Q(-139, 100), Q(1)]),
            poly_add(
                poly_mul([Q(-61, 4), Q(1)], [Q(-61, 4), Q(1)]),
                [Q(4)],
            ),
        ),
    )


def subtract_constant(p: list[Q], c: Q) -> list[Q]:
    result = p.copy()
    result[0] -= c
    return result


def freeze(values, case: Case, central: bool) -> list[Q]:
    result: list[Q] = []
    for i, value in enumerate(values):
        if i >= (3 if central else 2) and value > 0:
            value = 0.0
        if abs(value) < 1e-11:
            value = 0.0
        result.append(Q(f"{value:.12f}"))
    result[0] += case.slack
    return result


def solve_majorant(case: Case, central: bool):
    try:
        import numpy as np
        from scipy.optimize import linprog
    except ImportError as error:
        raise SystemExit("--write requires numpy and scipy") from error

    degree = case.degree
    endpoint = central_cos_endpoint(case.cap) if central else diffuse_cos_endpoint(case.cap)
    h = math.acos(float(endpoint))
    grid = 30000
    inside = np.linspace(-h, h, grid // 4 + 1)
    outside = np.r_[
        np.linspace(-math.pi, -h, 3 * grid // 8 + 1),
        np.linspace(h, math.pi, 3 * grid // 8 + 1),
    ]
    xs = np.unique(np.r_[inside, outside])
    matrix = np.array(
        [[1.0] + [math.cos(j * x) for j in range(1, degree + 1)] for x in xs]
    )
    rhs = (np.abs(xs) <= h + 1e-13).astype(float)
    objective = np.zeros(degree + 1)
    objective[0] = 1
    objective[1] = float(PHI1 if central else case.diffuse_moment)
    if central:
        objective[2] = float(PHI2)
        bounds = [(None, None), (0, None), (0, None)] + [
            (None, 0)
        ] * (degree - 2)
    else:
        bounds = [(None, None), (0, None)] + [(None, 0)] * (degree - 1)
    solution = linprog(
        objective, A_ub=-matrix, b_ub=-rhs, bounds=bounds, method="highs"
    )
    if not solution.success:
        raise RuntimeError(solution.message)
    return freeze(solution.x, case, central)


def exact_objective(case: Case, coefficients: list[Q], central: bool) -> Q:
    result = coefficients[0] + coefficients[1] * (
        PHI1 if central else case.diffuse_moment
    )
    if central:
        result += coefficients[2] * PHI2
    return result


def make_majorant_record(case: Case, central: bool) -> dict:
    coefficients = solve_majorant(case, central)
    endpoint = central_cos_endpoint(case.cap) if central else diffuse_cos_endpoint(case.cap)
    power = trig_to_power(coefficients)
    global_paths = adaptive_paths(power_to_bernstein(power, Q(-1), Q(1)))
    dominated = power.copy()
    dominated[0] -= 1
    domination_paths = adaptive_paths(power_to_bernstein(dominated, endpoint, Q(1)))
    return {
        "coefficients": [qtext(x) for x in coefficients],
        "endpoint": qtext(endpoint),
        "expectation_bound": qtext(exact_objective(case, coefficients, central)),
        "global_paths": global_paths,
        "domination_paths": domination_paths,
    }


def wrap_square_threshold(case: Case) -> Q:
    return 2 * (1 / case.split - case.cap) ** 2


def case_tail_bound(case: Case) -> Q:
    if case.tail_kind == "eighth_moment":
        return case.tail_denominator
    return TAIL_MOMENT_NUMERATOR / case.tail_denominator


def generate() -> dict:
    records = []
    for case in CASES:
        records.append(
            {
                "name": case.name,
                "cap": qtext(case.cap),
                "split": qtext(case.split),
                "degree": case.degree,
                "diffuse_moment": qtext(case.diffuse_moment),
                "slack": qtext(case.slack),
                "row_bound": qtext(case.row_bound),
                "rows_bits": [list(pair) for pair in case.rows_bits],
                "tail_kind": case.tail_kind,
                "tail_threshold": qtext(case.tail_threshold),
                "tail_denominator": qtext(case.tail_denominator),
                "wrap_square_threshold": qtext(wrap_square_threshold(case)),
                "central": make_majorant_record(case, True),
                "diffuse": make_majorant_record(case, False),
            }
        )
    return {
        "schema": 1,
        "pi_lower": qtext(PI_LOWER),
        "pi_upper": qtext(PI_UPPER),
        "phi1": qtext(PHI1),
        "phi2": qtext(PHI2),
        "tail_moment_numerator": qtext(TAIL_MOMENT_NUMERATOR),
        "cases": records,
    }


def verify_paths(power: list[Q], a: Q, b: Q, paths: list[str]) -> None:
    assert paths_form_full_tree(paths)
    root = power_to_bernstein(power, a, b)
    assert all(min(descend(root, path)) >= 0 for path in paths)


def verify_integer_paths(power: list[Q], a: Q, b: Q, paths: list[str]) -> None:
    root, denominator, *_ = integer_bernstein(power, a, b)
    assert denominator > 0
    assert all(min(descend_integer(root, path)) >= 0 for path in paths)


def verify_tail(case: Case) -> None:
    threshold = wrap_square_threshold(case)
    assert threshold >= case.tail_threshold
    if case.tail_kind == "eighth_moment":
        assert Q(105) / case.tail_threshold**4 < case.tail_denominator
        return
    difference = subtract_constant(tail_polynomial(), case.tail_denominator)
    paths = adaptive_paths(
        power_to_bernstein(difference, case.tail_threshold, Q(16))
    )
    verify_paths(difference, case.tail_threshold, Q(16), paths)
    shifted = compose_interval(difference, Q(16), Q(17))
    # compose_interval uses 16 + t; nonnegative power coefficients prove the
    # result for every t >= 0, not merely t <= 1.
    assert all(coefficient >= 0 for coefficient in shifted)


def verify_exp_bounds(case: Case) -> dict[str, int]:
    checks = {
        "phi1": (Q(12321, 20000), PHI1),
        "phi2": (Q(12321, 5000), PHI2),
        "diffuse": ((PI_LOWER * case.split) ** 2, case.diffuse_moment),
    }
    terms = {}
    for name, (argument, target) in checks.items():
        count = first_exp_terms(argument, 1 / target)
        assert exp_lower_sum(argument, count) > 1 / target
        terms[name] = count
    return terms


def verify_record(data: dict) -> dict:
    assert data["schema"] == 1
    assert parse_q(data["pi_lower"]) == PI_LOWER
    assert parse_q(data["pi_upper"]) == PI_UPPER
    assert parse_q(data["phi1"]) == PHI1
    assert parse_q(data["phi2"]) == PHI2
    assert parse_q(data["tail_moment_numerator"]) == TAIL_MOMENT_NUMERATOR
    summaries = []
    by_name = {case.name: case for case in CASES}
    record_names = [record["name"] for record in data["cases"]]
    assert len(record_names) == len(set(record_names))
    assert set(by_name) == set(record_names)
    for record in data["cases"]:
        case = by_name[record["name"]]
        assert parse_q(record["cap"]) == case.cap
        assert parse_q(record["split"]) == case.split
        assert record["degree"] == case.degree
        assert parse_q(record["diffuse_moment"]) == case.diffuse_moment
        assert parse_q(record["slack"]) == case.slack
        assert parse_q(record["row_bound"]) == case.row_bound
        assert record["rows_bits"] == [list(pair) for pair in case.rows_bits]
        assert record["tail_kind"] == case.tail_kind
        assert parse_q(record["tail_threshold"]) == case.tail_threshold
        assert parse_q(record["tail_denominator"]) == case.tail_denominator
        assert parse_q(record["wrap_square_threshold"]) == wrap_square_threshold(case)
        verify_tail(case)
        exp_terms = verify_exp_bounds(case)
        bounds = {}
        for name, central in (("central", True), ("diffuse", False)):
            majorant = record[name]
            coefficients = [parse_q(x) for x in majorant["coefficients"]]
            assert len(coefficients) == case.degree + 1
            assert coefficients[1] >= 0
            if central:
                assert coefficients[2] >= 0
                assert all(x <= 0 for x in coefficients[3:])
                endpoint = central_cos_endpoint(case.cap)
            else:
                assert all(x <= 0 for x in coefficients[2:])
                endpoint = diffuse_cos_endpoint(case.cap)
            assert parse_q(majorant["endpoint"]) == endpoint
            if central:
                assert endpoint <= central_cos_taylor(case.cap)
            else:
                assert endpoint <= diffuse_cos_taylor(case.cap)
            expectation = exact_objective(case, coefficients, central)
            assert parse_q(majorant["expectation_bound"]) == expectation
            power = trig_to_power(coefficients)
            verify_paths(power, Q(-1), Q(1), majorant["global_paths"])
            verify_integer_paths(power, Q(-1), Q(1), majorant["global_paths"])
            dominated = power.copy()
            dominated[0] -= 1
            verify_paths(dominated, endpoint, Q(1), majorant["domination_paths"])
            verify_integer_paths(
                dominated, endpoint, Q(1), majorant["domination_paths"]
            )
            bounds[name] = expectation
        small = bounds["central"] + case_tail_bound(case)
        assert small < case.row_bound
        assert bounds["diffuse"] < case.row_bound
        for rows, bits in case.rows_bits:
            assert case.row_bound**rows < Q(1, 2**bits)
            assert case.row_bound**rows >= Q(1, 2 ** (bits + 1))
        summaries.append(
            {
                "name": case.name,
                "central_plus_tail": qtext(small),
                "diffuse": qtext(bounds["diffuse"]),
                "row_bound": qtext(case.row_bound),
                "central_margin": qtext(case.row_bound - small),
                "diffuse_margin": qtext(case.row_bound - bounds["diffuse"]),
                "exp_taylor_terms": exp_terms,
                "certificate_leaves": {
                    name: {
                        "global": len(record[name]["global_paths"]),
                        "domination": len(record[name]["domination_paths"]),
                        "max_depth": max(
                            map(
                                len,
                                record[name]["global_paths"]
                                + record[name]["domination_paths"],
                            )
                        ),
                    }
                    for name in ("central", "diffuse")
                },
            }
        )
    return {"verified": True, "cases": summaries}


def emit_lean_sample(data: dict, output: Path) -> None:
    """Emit the limiting cap-0.42 central leaf used as a kernel benchmark."""
    record = next(case for case in data["cases"] if case["name"] == "cap42")
    coefficients = [parse_q(x) for x in record["central"]["coefficients"]]
    power = trig_to_power(coefficients)
    path = record["central"]["global_paths"][0]
    a, b = Q(-1), Q(1)
    for step in path:
        midpoint = (a + b) / 2
        if step == "0":
            b = midpoint
        else:
            a = midpoint
    bernstein = power_to_bernstein(power, a, b)
    power_numerators, power_denominator = common_integer_scale(power)
    bernstein_numerators, bernstein_denominator = common_integer_scale(bernstein)
    interval_denominator = math.lcm(a.denominator, (b - a).denominator)
    a_scaled = a * interval_denominator
    delta_scaled = (b - a) * interval_denominator
    assert a_scaled.denominator == 1 and delta_scaled.denominator == 1
    source = f'''/- This file is generated by scripts/derive_ternary_linf_frontiers.py. -/

import CertifiedJL.Certificates.Shared.TrigonometricBernstein

open scoped BigOperators Polynomial

namespace CertifiedJL.TrigonometricBernstein.GeneratedSample

private def cap42CentralPower : List ℚ :=
  {lean_list(power, lean_type="ℚ")}

private def cap42CentralPowerNumerators : List ℤ :=
  {lean_integer_list(power_numerators)}

private abbrev cap42CentralPowerDenominator : ℤ := {power_denominator}

private def cap42CentralLeaf000Numerators : List ℤ :=
  {lean_integer_list(bernstein_numerators)}

private abbrev cap42CentralLeaf000Denominator : ℤ := {bernstein_denominator}

private def cap42CentralLeaf000 : List ℚ :=
  cap42CentralLeaf000Numerators.map fun numerator =>
    (numerator : ℚ) / cap42CentralLeaf000Denominator

theorem cap42CentralPower_scale_check :
    integerScaleBlockCheck cap42CentralPower cap42CentralPowerNumerators
      cap42CentralPowerDenominator 0 74 = true := by
  decide +kernel

theorem cap42CentralPower_scale : ∀ k ≤ 73,
    cap42CentralPower.getD k 0 * cap42CentralPowerDenominator =
      cap42CentralPowerNumerators.getD k 0 := by
  intro k hk
  exact integerScaleBlockCheck_sound cap42CentralPower_scale_check
    k (by omega) (by omega)

theorem cap42CentralLeaf000_scale_check :
    integerScaleBlockCheck cap42CentralLeaf000 cap42CentralLeaf000Numerators
      cap42CentralLeaf000Denominator 0 74 = true := by
  decide +kernel

theorem cap42CentralLeaf000_scale : ∀ k ≤ 73,
    cap42CentralLeaf000.getD k 0 * cap42CentralLeaf000Denominator =
      cap42CentralLeaf000Numerators.getD k 0 := by
  intro k hk
  exact integerScaleBlockCheck_sound cap42CentralLeaf000_scale_check
    k (by omega) (by omega)

set_option maxHeartbeats 20000000 in
theorem cap42CentralLeaf000_identity_check :
    integerBernsteinIdentityBlockCheck cap42CentralPowerNumerators
      cap42CentralPowerDenominator {lean_q(a_scaled, "ℤ")}
      {lean_q(delta_scaled, "ℤ")} {lean_q(Q(interval_denominator), "ℤ")}
      73 cap42CentralLeaf000Numerators cap42CentralLeaf000Denominator 0 74 = true := by
  decide +kernel

theorem cap42CentralLeaf000_nonnegative_check :
    nonnegativeBlockCheck cap42CentralLeaf000 0 74 = true := by
  decide +kernel

theorem cap42CentralLeaf000_identity :
    affinePullbackQ (powerPolynomialQ cap42CentralPower)
        {lean_q(a, "ℚ")} {lean_q(b, "ℚ")} =
      bernsteinPolynomialQ 73 cap42CentralLeaf000 := by
  apply affinePullbackQ_eq_bernsteinPolynomialQ_of_integerCertificate
    (by decide) (by simp [cap42CentralLeaf000, cap42CentralLeaf000Numerators])
    (by decide) cap42CentralPower_scale cap42CentralLeaf000_scale
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    cap42CentralLeaf000_identity_check

theorem cap42CentralLeaf000_nonneg {{y : ℝ}}
    (hlo : ({lean_q(a, "ℝ")}) ≤ y) (hhi : y ≤ ({lean_q(b, "ℝ")})) :
    0 ≤ rationalPowerValue cap42CentralPower y := by
  apply rationalPowerValue_nonneg_on_interval (by norm_num)
    (by convert hlo using 1 <;> norm_num)
    (by convert hhi using 1 <;> norm_num)
    cap42CentralLeaf000_identity
  intro k hk
  exact nonnegativeBlockCheck_sound cap42CentralLeaf000_nonnegative_check
    k (by omega) (by omega)

end CertifiedJL.TrigonometricBernstein.GeneratedSample
'''
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(source)


def path_interval(a: Q, b: Q, path: str) -> tuple[Q, Q]:
    for step in path:
        midpoint = (a + b) / 2
        if step == "0":
            b = midpoint
        else:
            a = midpoint
    return a, b


def family_name(case_name: str, kind: str) -> str:
    return case_name[0].upper() + case_name[1:] + kind.capitalize()


def leaf_source(
    family: str,
    kind: str,
    index: int,
    degree: int,
    power: list[Q],
    root_a: Q,
    root_b: Q,
    path: str,
) -> str:
    a, b = path_interval(root_a, root_b, path)
    bernstein = descend(power_to_bernstein(power, root_a, root_b), path)
    bernstein_numerators, bernstein_denominator = common_integer_scale(bernstein)
    interval_denominator = math.lcm(a.denominator, (b - a).denominator)
    a_scaled = a * interval_denominator
    delta_scaled = (b - a) * interval_denominator
    assert a_scaled.denominator == 1 and delta_scaled.denominator == 1
    a_numerator = a_scaled.numerator
    delta_numerator = delta_scaled.numerator
    prefix = "global" if kind == "global" else "domination"
    stem = f"{prefix}Leaf{index:02d}"
    power_expression = "power" if kind == "global" else "subtractConstant power 1"
    power_numerators = (
        "powerNumerators" if kind == "global" else "dominationPowerNumerators"
    )
    power_scale = (
        "powerIntegerScale" if kind == "global" else "dominationPowerIntegerScale"
    )
    length_simp = "degree, power" if kind == "global" else "degree, subtractConstant"
    return f'''/- This file is generated by scripts/derive_ternary_linf_frontiers.py. -/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.{family}.PowerScale

open scoped BigOperators Polynomial
open CertifiedJL.TrigonometricBernstein

set_option linter.style.longLine false

namespace CertifiedJL.TernaryLInfTwoDecimal.{family}

private def {stem}BernsteinNumerators : List ℤ :=
  {lean_integer_list(bernstein_numerators)}

private abbrev {stem}BernsteinDenominator : ℤ := {bernstein_denominator}

private def {stem}Bernstein : List ℚ :=
  {stem}BernsteinNumerators.map fun numerator =>
    (numerator : ℚ) / {stem}BernsteinDenominator

theorem {stem}BernsteinScaleCheck :
    integerScaleBlockCheck {stem}Bernstein {stem}BernsteinNumerators
      {stem}BernsteinDenominator 0 (degree + 1) = true := by
  decide +kernel

theorem {stem}BernsteinScale : ∀ k ≤ degree,
    {stem}Bernstein.getD k 0 * {stem}BernsteinDenominator =
      {stem}BernsteinNumerators.getD k 0 := by
  intro k hk
  exact integerScaleBlockCheck_sound {stem}BernsteinScaleCheck
    k (by omega) (by simpa [degree] using Nat.lt_succ_iff.mpr hk)

set_option maxHeartbeats 40000000 in
-- The quadratic identity check now uses common-denominator integer arithmetic.
set_option maxRecDepth 1000000 in
theorem {stem}IdentityCheck :
    integerBernsteinIdentityBlockCheck {power_numerators} powerDenominator
      {lean_q(Q(a_numerator), "ℤ")} {lean_q(Q(delta_numerator), "ℤ")}
      {lean_q(Q(interval_denominator), "ℤ")} degree
      {stem}BernsteinNumerators {stem}BernsteinDenominator 0 (degree + 1) = true := by
  decide +kernel

theorem {stem}NonnegativeCheck :
    nonnegativeBlockCheck {stem}Bernstein 0 (degree + 1) = true := by
  decide +kernel

theorem {stem}Identity :
    affinePullbackQ (powerPolynomialQ ({power_expression}))
        {lean_q(a, "ℚ")} {lean_q(b, "ℚ")} =
      bernsteinPolynomialQ degree {stem}Bernstein := by
  apply affinePullbackQ_eq_bernsteinPolynomialQ_of_integerCertificate
    (by simp [{length_simp}])
    (by simp [degree, {stem}Bernstein, {stem}BernsteinNumerators])
    (by simp [degree, {power_numerators}]) {power_scale} {stem}BernsteinScale
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    {stem}IdentityCheck

theorem {stem}Nonneg {{y : ℝ}}
    (hlo : {lean_cast_q(a)} ≤ y) (hhi : y ≤ {lean_cast_q(b)}) :
    0 ≤ rationalPowerValue ({power_expression}) y := by
  apply rationalPowerValue_nonneg_on_interval (by norm_num) hlo hhi {stem}Identity
  intro k hk
  exact nonnegativeBlockCheck_sound {stem}NonnegativeCheck
    k (by omega) (by simpa [degree] using hk)

theorem {stem}Tree :
    NonnegativeTree (rationalPowerValue ({power_expression}))
      {lean_q(a, "ℚ")} {lean_q(b, "ℚ")} :=
  .leaf (fun _y hlo hhi => {stem}Nonneg hlo hhi)

end CertifiedJL.TernaryLInfTwoDecimal.{family}
'''


def tree_term(paths: list[str], prefix: str, theorem_prefix: str) -> str:
    """Build a structurally full `NonnegativeTree` proof term."""
    if paths == [prefix]:
        index = tree_term.path_indices[prefix]
        if prefix == "":
            return f"{theorem_prefix}Leaf{index:02d}Tree"
        return (
            f"(by\n        convert {theorem_prefix}Leaf{index:02d}Tree using 1\n"
            "        all_goals norm_num)"
        )
    left = [path for path in paths if path.startswith(prefix + "0")]
    right = [path for path in paths if path.startswith(prefix + "1")]
    assert left and right
    return (
        ".branch\n      ("
        + tree_term(left, prefix + "0", theorem_prefix)
        + ")\n      ("
        + tree_term(right, prefix + "1", theorem_prefix)
        + ")"
    )


tree_term.path_indices = {}  # type: ignore[attr-defined]


def verified_source(
    family: str,
    degree: int,
    endpoint: Q,
    global_paths: list[str],
    domination_paths: list[str],
) -> str:
    imports = [
        f"import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay."
        f"{family}.FourierBridge"
    ]
    for prefix, paths in (("Global", global_paths), ("Domination", domination_paths)):
        for index, _ in enumerate(paths):
            imports.append(
                f"import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay."
                f"{family}.{prefix}Leaf{index:02d}"
            )
    tree_term.path_indices = {  # type: ignore[attr-defined]
        path: index for index, path in enumerate(global_paths)
    }
    global_tree = tree_term(global_paths, "", "global")
    tree_term.path_indices = {  # type: ignore[attr-defined]
        path: index for index, path in enumerate(domination_paths)
    }
    domination_tree = tree_term(domination_paths, "", "domination")
    return "\n".join(imports) + f'''

open CertifiedJL.TrigonometricBernstein

namespace CertifiedJL.TernaryLInfTwoDecimal.{family}

theorem globalTree :
    NonnegativeTree (rationalPowerValue power) (-1) 1 := by
  exact {global_tree}

theorem rawNonnegative {{y : ℝ}} (hlo : (((-1 : ℚ)) : ℝ) ≤ y)
    (hhi : y ≤ (((1 : ℚ)) : ℝ)) :
    0 ≤ rationalPowerValue power y :=
  globalTree.nonneg hlo hhi

theorem dominationTree :
    NonnegativeTree (rationalPowerValue (subtractConstant power 1))
      {lean_q(endpoint, "ℚ")} 1 := by
  exact {domination_tree}

theorem rawDominatesOne {{y : ℝ}} (hlo : {lean_cast_q(endpoint)} ≤ y)
    (hhi : y ≤ (((1 : ℚ)) : ℝ)) : 1 ≤ rationalPowerValue power y := by
  have h := dominationTree.nonneg hlo hhi
  rw [rationalPowerValue_subtractConstant_of_ne_nil (by simp [power]) 1] at h
  norm_num at h
  exact h

theorem cosineNonnegative (x : ℝ) :
    0 ≤ rationalCosineValue fourier x := by
  rw [← rationalPowerValue_cos_eq_rationalCosineValue fourierPowerCheck x]
  exact rawNonnegative (by simpa using Real.neg_one_le_cos x)
    (by simpa using Real.cos_le_one x)

theorem cosineDominatesOne {{x : ℝ}} (hx : {lean_cast_q(endpoint)} ≤ Real.cos x) :
    1 ≤ rationalCosineValue fourier x := by
  rw [← rationalPowerValue_cos_eq_rationalCosineValue fourierPowerCheck x]
  exact rawDominatesOne hx (by simpa using Real.cos_le_one x)

end CertifiedJL.TernaryLInfTwoDecimal.{family}
'''


def tail_verified_source(record: dict) -> tuple[str, str]:
    """Emit the low-degree unbounded tail lower-bound certificate."""
    assert record["tail_kind"] == "degree_ten"
    family = family_name(record["name"], "tail")
    threshold = parse_q(record["tail_threshold"])
    denominator = parse_q(record["tail_denominator"])
    power = subtract_constant(tail_polynomial(), denominator)
    degree = len(power) - 1
    assert degree == 5
    root_upper = Q(16)
    paths = adaptive_paths(power_to_bernstein(power, threshold, root_upper))
    assert paths_form_full_tree(paths)
    declarations: list[str] = []
    for index, path in enumerate(paths):
        a, b = path_interval(threshold, root_upper, path)
        bernstein = descend(
            power_to_bernstein(power, threshold, root_upper), path
        )
        stem = f"tailLeaf{index:02d}"
        declarations.append(
            f'''private def {stem}Bernstein : List ℚ :=
  {lean_list(bernstein, lean_type="ℚ")}

theorem {stem}IdentityCheck :
    bernsteinIdentityBlockCheck tailPower {lean_q(a, "ℚ")} {lean_q(b, "ℚ")}
      degree {stem}Bernstein 0 (degree + 1) = true := by
  decide +kernel

theorem {stem}NonnegativeCheck :
    nonnegativeBlockCheck {stem}Bernstein 0 (degree + 1) = true := by
  decide +kernel

theorem {stem}Identity :
    affinePullbackQ (powerPolynomialQ tailPower) {lean_q(a, "ℚ")} {lean_q(b, "ℚ")} =
      bernsteinPolynomialQ degree {stem}Bernstein := by
  apply affinePullbackQ_eq_bernsteinPolynomialQ (by simp [degree, tailPower])
    (by simp [degree, {stem}Bernstein])
  intro k hk
  exact bernsteinIdentityBlockCheck_sound {stem}IdentityCheck
    k (by omega) (by simpa [degree] using Nat.lt_succ_iff.mpr hk)

theorem {stem}Nonneg {{y : ℝ}}
    (hlo : {lean_cast_q(a)} ≤ y) (hhi : y ≤ {lean_cast_q(b)}) :
    0 ≤ rationalPowerValue tailPower y := by
  apply rationalPowerValue_nonneg_on_interval (by norm_num) hlo hhi {stem}Identity
  intro k hk
  exact nonnegativeBlockCheck_sound {stem}NonnegativeCheck
    k (by omega) (by simpa [degree] using hk)

theorem {stem}Tree :
    NonnegativeTree (rationalPowerValue tailPower)
      {lean_q(a, "ℚ")} {lean_q(b, "ℚ")} :=
  .leaf (fun _y hlo hhi => {stem}Nonneg hlo hhi)'''
        )
    tree_term.path_indices = {  # type: ignore[attr-defined]
        path: index for index, path in enumerate(paths)
    }
    tree = tree_term(paths, "", "tail")
    shifted = compose_interval(power, root_upper, root_upper + 1)
    assert all(coefficient >= 0 for coefficient in shifted)
    source = f'''/- This file is generated by scripts/derive_ternary_linf_frontiers.py. -/

import CertifiedJL.Certificates.Shared.TrigonometricBernstein

open scoped BigOperators Polynomial
open CertifiedJL.TrigonometricBernstein

set_option linter.style.longLine false

namespace CertifiedJL.TernaryLInfTwoDecimal.{family}

abbrev degree : ℕ := {degree}

abbrev tailPower : List ℚ :=
  {lean_list(power, lean_type="ℚ")}

abbrev shiftedPower : List ℚ :=
  {lean_list(shifted, lean_type="ℚ")}

{chr(10).join(declarations)}

theorem coreTree :
    NonnegativeTree (rationalPowerValue tailPower)
      {lean_q(threshold, "ℚ")} {lean_q(root_upper, "ℚ")} := by
  exact {tree}

theorem coreNonnegative {{x : ℝ}}
    (hlo : {lean_cast_q(threshold)} ≤ x) (hhi : x ≤ (16 : ℝ)) :
    0 ≤ rationalPowerValue tailPower x :=
  coreTree.nonneg hlo hhi

theorem shiftedIdentity (t : ℝ) :
    rationalPowerValue tailPower (16 + t) =
      rationalPowerValue shiftedPower t := by
  norm_num [rationalPowerValue, powerPolynomialQ, tailPower, shiftedPower,
    Finset.sum_range_succ]
  ring

theorem shiftedNonnegative {{t : ℝ}} (ht : 0 ≤ t) :
    0 ≤ rationalPowerValue shiftedPower t := by
  norm_num [rationalPowerValue, powerPolynomialQ, shiftedPower,
    Finset.sum_range_succ]
  positivity

theorem nonnegativeAbove {{x : ℝ}} (hx : {lean_cast_q(threshold)} ≤ x) :
    0 ≤ rationalPowerValue tailPower x := by
  by_cases hcore : x ≤ 16
  · exact coreNonnegative hx hcore
  · have ht : 0 ≤ x - 16 := by linarith
    rw [show x = 16 + (x - 16) by ring, shiftedIdentity]
    exact shiftedNonnegative ht

end CertifiedJL.TernaryLInfTwoDecimal.{family}
'''
    return family, source


def generated_lean_sources(data: dict) -> dict[Path, str]:
    sources: dict[Path, str] = {}
    root_imports = []
    for record in data["cases"]:
        degree = record["degree"]
        for majorant_kind in ("central", "diffuse"):
            family = family_name(record["name"], majorant_kind)
            majorant = record[majorant_kind]
            coefficients = [parse_q(x) for x in majorant["coefficients"]]
            power = trig_to_power(coefficients)
            assert len(power) <= degree + 1
            power.extend([Q(0)] * (degree + 1 - len(power)))
            power_numerators, power_denominator = common_integer_scale(power)
            domination_power_numerators = power_numerators.copy()
            domination_power_numerators[0] -= power_denominator
            data_source = f'''/- This file is generated by scripts/derive_ternary_linf_frontiers.py. -/

import CertifiedJL.Certificates.Shared.TrigonometricBernstein

set_option linter.style.longLine false

namespace CertifiedJL.TernaryLInfTwoDecimal.{family}

abbrev degree : ℕ := {degree}

abbrev power : List ℚ :=
  {lean_list(power, lean_type="ℚ")}

abbrev powerDenominator : ℤ := {power_denominator}

abbrev powerNumerators : List ℤ :=
  {lean_integer_list(power_numerators)}

abbrev dominationPowerNumerators : List ℤ :=
  {lean_integer_list(domination_power_numerators)}

abbrev fourier : List ℚ :=
  {lean_list(coefficients, lean_type="ℚ")}

abbrev endpoint : ℚ := {lean_q(parse_q(majorant["endpoint"]), "ℚ")}

abbrev expectationBound : ℚ :=
  {lean_q(parse_q(majorant["expectation_bound"]), "ℚ")}

abbrev phiOneBound : ℚ := {lean_q(parse_q(data["phi1"]), "ℚ")}

abbrev phiTwoBound : ℚ := {lean_q(parse_q(data["phi2"]), "ℚ")}

abbrev diffuseMomentBound : ℚ :=
  {lean_q(parse_q(record["diffuse_moment"]), "ℚ")}

end CertifiedJL.TernaryLInfTwoDecimal.{family}
'''
            sources[Path("Data") / family / "Data.lean"] = data_source
            power_scale_source = f'''/- This file is generated by scripts/derive_ternary_linf_frontiers.py. -/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.{family}.Data

open CertifiedJL.TrigonometricBernstein

namespace CertifiedJL.TernaryLInfTwoDecimal.{family}

theorem powerIntegerScaleCheck :
    integerScaleBlockCheck power powerNumerators powerDenominator
      0 (degree + 1) = true := by
  decide +kernel

theorem powerIntegerScale : ∀ k ≤ degree,
    power.getD k 0 * powerDenominator = powerNumerators.getD k 0 := by
  intro k hk
  exact integerScaleBlockCheck_sound powerIntegerScaleCheck
    k (by omega) (by simpa [degree] using Nat.lt_succ_iff.mpr hk)

theorem dominationPowerIntegerScaleCheck :
    integerScaleBlockCheck (subtractConstant power 1) dominationPowerNumerators
      powerDenominator 0 (degree + 1) = true := by
  decide +kernel

theorem dominationPowerIntegerScale : ∀ k ≤ degree,
    (subtractConstant power 1).getD k 0 * powerDenominator =
      dominationPowerNumerators.getD k 0 := by
  intro k hk
  exact integerScaleBlockCheck_sound dominationPowerIntegerScaleCheck
    k (by omega) (by simpa [degree] using Nat.lt_succ_iff.mpr hk)

end CertifiedJL.TernaryLInfTwoDecimal.{family}
'''
            sources[Path("Replay") / family / "PowerScale.lean"] = power_scale_source
            if majorant_kind == "central":
                tail_start = 3
                contract_statement = (
                    "CentralFourierContract fourier degree phiOneBound "
                    "phiTwoBound expectationBound"
                )
                contract_fields = """by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, by decide +kernel⟩"""
            else:
                tail_start = 2
                contract_statement = (
                    "DiffuseFourierContract fourier degree diffuseMomentBound "
                    "expectationBound"
                )
                contract_fields = """by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    ?_, by decide +kernel⟩"""
            bridge_source = f'''/- This file is generated by scripts/derive_ternary_linf_frontiers.py. -/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Data.{family}.Data

open CertifiedJL.TrigonometricBernstein

namespace CertifiedJL.TernaryLInfTwoDecimal.{family}

set_option maxHeartbeats 40000000 in
-- Kernel reduction checks that the frozen Fourier data converts to this exact power list.
set_option maxRecDepth 1000000 in
theorem fourierPowerCheck :
    chebyshevCombinationPower fourier = power := by
  decide +kernel

theorem fourierTailNonpositiveCheck :
    nonpositiveBlockCheck fourier {tail_start}
      (degree + 1 - {tail_start}) = true := by
  decide +kernel

theorem fourierContract :
    {contract_statement} := {contract_fields}
  intro j hjStart hjLength
  apply nonpositiveBlockCheck_sound fourierTailNonpositiveCheck j hjStart
  have hlength : fourier.length = degree + 1 := by decide +kernel
  rw [hlength] at hjLength
  have hdegree : {tail_start} ≤ degree + 1 := by decide +kernel
  omega

end CertifiedJL.TernaryLInfTwoDecimal.{family}
'''
            sources[Path("Replay") / family / "FourierBridge.lean"] = bridge_source
            for proof_kind, root_a, root_b, paths in (
                ("global", Q(-1), Q(1), majorant["global_paths"]),
                (
                    "domination",
                    parse_q(majorant["endpoint"]),
                    Q(1),
                    majorant["domination_paths"],
                ),
            ):
                leaf_power = power if proof_kind == "global" else subtract_constant(power, Q(1))
                for index, path in enumerate(paths):
                    filename = (
                        ("Global" if proof_kind == "global" else "Domination")
                        + f"Leaf{index:02d}.lean"
                    )
                    sources[Path("Replay") / family / filename] = leaf_source(
                        family,
                        proof_kind,
                        index,
                        degree,
                        leaf_power,
                        root_a,
                        root_b,
                        path,
                    )
            sources[Path("Replay") / family / "Verified.lean"] = verified_source(
                family,
                degree,
                parse_q(majorant["endpoint"]),
                majorant["global_paths"],
                majorant["domination_paths"],
            )
            root_imports.append(
                f"import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay."
                f"{family}.Verified"
            )
        if record["tail_kind"] == "degree_ten":
            tail_family, tail_source = tail_verified_source(record)
            sources[Path("Replay") / tail_family / "Verified.lean"] = tail_source
            root_imports.append(
                "import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay."
                f"{tail_family}.Verified"
            )
    sources[Path("Replay.lean")] = "\n".join(root_imports) + "\n"
    return sources


def write_lean_certificates(data: dict, output_root: Path, check: bool) -> None:
    sources = generated_lean_sources(data)
    failures = []
    for relative, source in sources.items():
        path = output_root / relative
        if check:
            if not path.is_file() or path.read_text() != source:
                failures.append(str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
    if failures:
        raise SystemExit("generated Lean certificates differ: " + ", ".join(failures))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--emit-lean-sample", type=Path)
    parser.add_argument(
        "--emit-lean-certificates", type=Path, nargs="?", const=DEFAULT_LEAN_ROOT
    )
    parser.add_argument(
        "--check-lean-certificates", type=Path, nargs="?", const=DEFAULT_LEAN_ROOT
    )
    args = parser.parse_args()
    if (
        not args.write
        and not args.verify
        and args.emit_lean_sample is None
        and args.emit_lean_certificates is None
        and args.check_lean_certificates is None
    ):
        parser.error(
            "select --write, --verify, --emit-lean-sample, "
            "--emit-lean-certificates, and/or --check-lean-certificates"
        )
    if args.write:
        data = generate()
        args.artifact.parent.mkdir(parents=True, exist_ok=True)
        args.artifact.write_text(json.dumps(data, indent=2) + "\n")
    if args.verify:
        data = json.loads(args.artifact.read_text())
        print(json.dumps(verify_record(data), indent=2))
    if args.emit_lean_sample is not None:
        data = json.loads(args.artifact.read_text())
        verify_record(data)
        emit_lean_sample(data, args.emit_lean_sample)
    if args.emit_lean_certificates is not None:
        data = json.loads(args.artifact.read_text())
        verify_record(data)
        write_lean_certificates(data, args.emit_lean_certificates, check=False)
    if args.check_lean_certificates is not None:
        data = json.loads(args.artifact.read_text())
        verify_record(data)
        write_lean_certificates(data, args.check_lean_certificates, check=True)


if __name__ == "__main__":
    main()
