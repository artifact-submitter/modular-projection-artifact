#!/usr/bin/env python3
"""Bounded exact no-wrap searches; these finite negatives are not optimality proofs."""

import argparse
from fractions import Fraction as F
from itertools import combinations_with_replacement
import json
from math import comb

from counterexample_probability import (
    compare_dyadic_budget,
    identical_energy_convolution,
    squared_energy_distribution,
    weighted_row_sums,
)


def row_counts(vector):
    """Compatibility wrapper for the reusable exact helper."""
    return weighted_row_sums(vector)


def squared_sum_counts(row, rows, cutoff):
    """Discard sums above cutoff: squared increments cannot return below it."""
    return identical_energy_convolution(row, rows, cutoff)


def exceeds(probability, bits):
    """Preserve the historical strict-excess query (not theorem refutation)."""
    return probability.numerator * 2**bits > probability.denominator


def linf_search():
    caps = list(map(F, ('21/50', '43/100', '9/20', '47/100', '49/100', '1/2', '67/200')))
    best = {cap: (F(0), None) for cap in caps}
    cases = 0
    for dimension in range(1, 9):
        for vector in combinations_with_replacement((1, 2, 3), dimension):
            cases += 1
            counts = row_counts(vector)
            normsq = sum(x*x for x in vector)
            for cap in caps:
                # Only the unmasked primitive is retained.  The old 67/200
                # branch optimized arbitrary interval endpoints and did not
                # construct an admissible integer mask.
                good = sum(w for x, w in counts.items() if
                           x*x * cap.denominator**2 <= cap.numerator**2 * normsq)
                probability = F(good, 4**dimension)
                if probability > best[cap][0]:
                    best[cap] = probability, vector
    return {'vectors': cases, 'results': [
        {'cap': str(cap), 'mask': 'zero', 'row_probability': str(p),
         'vector': vector, 'exceeds_128_bits': exceeds(p**256, 128),
         'exceeds_130_bits': exceeds(p**256, 130)}
        for cap, (p, vector) in best.items()]}


def l2_search():
    best = {27: (F(0), None), 30: (F(0), None), 337: (F(0), None)}
    cases = 0
    for dimension in range(1, 5):
        for vector in combinations_with_replacement((1, 2, 3), dimension):
            counts = row_counts(vector)
            normsq = sum(x*x for x in vector)
            # Preserve only the valid unmasked primitive.  Previous odd
            # ``shift2`` values encoded inadmissible half-integer masks.
            for shift2 in (0,):
                cases += 1
                row = squared_energy_distribution(counts)
                cutoff = 337 * normsq
                distribution = squared_sum_counts(row, 256, cutoff)
                denominator = sum(counts.values())**256
                for floor in (27, 30):
                    p = F(sum(w for x, w in distribution.items()
                              if x < floor * normsq), denominator)
                    if p > best[floor][0]:
                        best[floor] = p, (vector, '0')
                p = 1 - F(sum(distribution.values()), denominator)
                if p > best[337][0]:
                    best[337] = p, (vector, '0')
    return {'vector_shift_cases': cases, 'results': [
        {'threshold': threshold, 'vector_shift': witness,
         'probability_numerator': str(p.numerator), 'probability_denominator': str(p.denominator),
         'exceeds_128_bits': exceeds(p, 128)}
        for threshold, (p, witness) in best.items()]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--linf-only', action='store_true', help='skip the slower squared-sum search')
    args = parser.parse_args()
    result = {'schema_version': 1, 'rows': 256, 'law': 'balanced ternary (-1,0,1) weights (1,2,1)',
              'scope': 'unmasked no-wrap, input-relative norm, finite directions only; not a public-threshold witness validator',
              'linf': linf_search(), 'singleton': [
                  {'strict_floor': floor, 'numerator': str(sum(comb(256, k) for k in range(floor))),
                   'denominator': str(2**256),
                   'exceeds_128_bits': sum(comb(256, k) for k in range(floor)) > 2**128}
                  for floor in (27, 29, 30, 31)]}
    if not args.linf_only:
        result['l2'] = l2_search()
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
