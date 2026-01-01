#!/usr/bin/env python3
"""Exact research checks, NOT Lean proofs. See docs/three-axis-tightness-handoff.md."""

from fractions import Fraction
import hashlib
from math import comb, factorial, log2

from counterexample_probability import (
    centered_residue_counts,
    compare_dyadic_budget,
    identical_energy_convolution,
    squared_energy_distribution,
    weighted_row_sums,
)


def require(condition, message):
    """Keep authoritative research checks active under ``python -O``."""
    if not condition:
        raise RuntimeError(message)


def q9_compact_certificate():
    """Return the reviewed 264-term sub-sum used by the Lean numeric leaf."""
    weights = {0: 607812102, 1: 1154294424, 4: 999371554,
               9: 823843664, 16: 709645552}
    numerator = 0
    terms = 0
    fact256 = factorial(256)
    for n9 in range(12, 15):
        for n4 in range(45, 56):
            center = 431 - 9 * n9 - 4 * n4
            for n1 in range(center - 7, center + 1):
                n16 = 2
                n0 = 256 - n16 - n9 - n4 - n1
                require(n0 >= 0, "compact q9 certificate has a negative multiplicity")
                energy = 16 * n16 + 9 * n9 + 4 * n4 + n1
                require(energy <= 463, "compact q9 certificate crosses the strict cutoff")
                multinomial = fact256 // (
                    factorial(n0) * factorial(n1) * factorial(n4)
                    * factorial(n9) * factorial(n16)
                )
                numerator += (
                    multinomial * weights[0]**n0 * weights[1]**n1
                    * weights[4]**n4 * weights[9]**n9 * weights[16]**n16
                )
                terms += 1
    digest = hashlib.sha256(str(numerator).encode("ascii")).hexdigest()
    require(terms == 264, "compact q9 certificate must contain exactly 264 terms")
    require(numerator > 2**8064, "compact q9 certificate lost its strict dyadic excess")
    require(digest == "3e0c9b7b27797f0a8f3e464119e08bc48ecd0a5c688225c672624ad36a7e1130",
            "compact q9 certificate decimal digest changed")
    return terms, numerator, digest


def modulus_two_witness():
    # Independent constructions of the weighted one-row residue distribution.
    binomial = [0] * 9
    for k in range(33):
        binomial[(k - 16) % 9] += comb(32, k)
    direct = [1] + [0] * 8
    for _ in range(16):
        direct = [direct[(r - 1) % 9] + 2 * direct[r] + direct[(r + 1) % 9]
                  for r in range(9)]
    helper = centered_residue_counts(weighted_row_sums([1] * 16), 9)
    helper_residues = [helper[r if r <= 4 else r - 9] for r in range(9)]
    require(binomial == direct == helper_residues,
            "independent q=9 row distributions disagree")
    energy = squared_energy_distribution(helper)
    expected = {0: 607812102, 1: 1154294424, 4: 999371554,
                9: 823843664, 16: 709645552}
    require(energy == expected, "unexpected q=9 squared-energy histogram")
    require(sum(energy.values()) == 2**32, "q=9 row mass is not 2^32")
    # Nonnegative energies permit exact truncation at the strict cutoff 464.
    counts = identical_energy_convolution(energy, 256, cutoff=463)
    numerator = sum(counts.values())
    require(compare_dyadic_budget(Fraction(numerator, 2**8192), 128),
            "q=9 witness does not refute the strict 128-bit guarantee")
    require(numerator > 2**8064, "q=9 witness lost its strict excess")
    q9_compact_certificate()
    print('M=2, m=256, c=29: exact P > 2^-128; reporting log2(P) =',
          log2(numerator) - 8192)


def singleton_witnesses():
    cases = {
        'norm': [(192, 14, 128), (256, 13, 192), (384, 45, 192), (512, 59, 256)],
        'security': [(256, 29, 132), (256, 9, 208), (384, 43, 197), (512, 57, 261)],
    }
    for axis, targets in cases.items():
        for rows, threshold, bits in targets:
            numerator = sum(comb(rows, k) for k in range(threshold))
            require(numerator * 2**bits > 2**rows,
                    f"singleton witness no longer exceeds its budget: {(rows, threshold, bits)}")
            print(axis, (rows, threshold, bits), 'exact strict excess; reporting bits =',
                  rows - log2(numerator))


if __name__ == '__main__':
    modulus_two_witness()
    singleton_witnesses()
