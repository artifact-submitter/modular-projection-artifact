#!/usr/bin/env python3
"""Canonical discovery of Lean roots built by fast validation."""

from __future__ import annotations

from validation_roots import targets

# Exact negative-result certificates and the experimental closed-core replay
# are outside the current positive-result provider boundaries. Neither may
# enter Fast.
EXACT_ONLY_ROOTS = {
    "CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.Verified",
    "CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Replay",
}


def fast_validation_roots() -> set[str]:
    roots = set(targets("fast"))
    if not roots:
        raise SystemExit("no fast Lean validation roots are registered")
    return roots
