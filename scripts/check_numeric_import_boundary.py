#!/usr/bin/env python3
"""Keep lower-cover kernel computations independent of probability soundness."""
from __future__ import annotations

from check_fast_import_boundary import graph, path_to_forbidden

PREFIX = "CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant."
NEAR_PREFIX = "CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near."
ARITHMETIC_ROOTS = {
    PREFIX + "Data.Numeric",
    PREFIX + "Data.ConstantNumericData",
    PREFIX + "Data.TargetNumericData",
}
FOURIER_ROOTS = {
    PREFIX + "Data.CappedFourierNumeric128Data",
    PREFIX + "Data.CappedFourierNumeric256Bits192Data",
    PREFIX + "Data.SingletonFourierNumeric128Data",
    PREFIX + "Data.SingletonPhaseFourierNumeric256Bits192Data",
}
CORE_ROOTS = ARITHMETIC_ROOTS | FOURIER_ROOTS
ALLOWED_EXECUTABLE_ARITHMETIC = {
    "CertifiedJL.Arithmetic.Interval.Dyadic",
    "CertifiedJL.Arithmetic.Interval.Interval",
    "CertifiedJL.Arithmetic.Interval.ReflectionData",
    "CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExpData",
    "CertifiedJL.Arithmetic.Transcendental.Exponential.ExpData",
    "CertifiedJL.Arithmetic.Transcendental.SquareRoot.SqrtData",
    "CertifiedJL.Arithmetic.Transcendental.Trigonometric.TrigData",
}


def boundary_failures(imports: dict[str, tuple[str, ...]]) -> list[str]:
    modules = set(imports)
    modules.update(imported for direct in imports.values() for imported in direct)
    dominant_data_roots = CORE_ROOTS | {
        name
        for name in imports
        if name.startswith(PREFIX + "Data.")
    }
    certificate_data_roots = {
        name for name in imports
        if name.startswith("CertifiedJL.Certificates.")
        and ".Data." in f".{name}."
    }
    replay_roots = {
        name for name in imports
        if name.startswith(PREFIX + "Replay.ConstantDirectCover")
        and "Shard" in name
    }
    near_roots = {
        name for name in imports
        if name.startswith(NEAR_PREFIX + "Data.")
        or name.startswith(NEAR_PREFIX + "Replay.ThresholdNearCoarseShard")
    }
    roots = certificate_data_roots | replay_roots | near_roots
    forbidden = {
        name for name in modules
        if name.startswith((
            "CertifiedJL.Projection.",
            "CertifiedJL.Probability.",
            "CertifiedJL.Analysis.",
        ))
    }
    non_executable_arithmetic = {
        name for name in modules
        if name.startswith("CertifiedJL.Arithmetic.")
        and name not in ALLOWED_EXECUTABLE_ARITHMETIC
    }
    upper_certificate_layers = {
        name for name in modules
        if name.startswith("CertifiedJL.Certificates.")
        and any(
            marker in f".{name}." for marker in (".Soundness.", ".Replay.")
        )
    }
    failures = ["missing numeric root: " + root for root in sorted(CORE_ROOTS - imports.keys())]
    for root in sorted(roots):
        excluded = set(forbidden)
        if root in dominant_data_roots or root in replay_roots or root in near_roots:
            excluded |= non_executable_arithmetic
        if root in certificate_data_roots:
            excluded |= upper_certificate_layers
        path = path_to_forbidden(imports, root, excluded)
        if path:
            failures.append(" -> ".join(path))
    return failures


def main() -> None:
    imports = graph()
    failures = boundary_failures(imports)
    if failures:
        raise SystemExit("numeric import boundary error:\n" + "\n".join(failures))
    print("numeric import boundary verified: lower-cover computations exclude analytic soundness")


if __name__ == "__main__":
    main()
