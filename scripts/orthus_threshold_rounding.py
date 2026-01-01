#!/usr/bin/env python3
"""Exact scalar threshold/modulus lower bounds, not complete Orthus parameters."""
import argparse
from fractions import Fraction
import json


def rounded_parameters(norm, cap, margin):
    if norm < 0:
        raise ValueError('honest norm bound must be nonnegative')
    acceptance = Fraction(39, 4) * norm
    ratio = acceptance / cap
    threshold = max(1, -(-ratio.numerator // ratio.denominator))
    lower = margin * threshold
    odd_modulus = lower if lower % 2 else lower + 1
    return {'acceptance_radius': str(acceptance), 'public_threshold': threshold,
            'minimum_odd_modulus': odd_modulus,
            'minimum_odd_modulus_bit_length': odd_modulus.bit_length()}


def compare(norm):
    return {'honest_norm_bound': str(norm),
            'scope': 'scalar closed-acceptance adapter only; no SIS, ring, primality, packing or size claim',
            'printed_orthus': rounded_parameters(norm, Fraction(37, 50), 91),
            'certified_replacement': rounded_parameters(norm, Fraction(21, 50), 2)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('norm', type=Fraction, nargs='+', help='explicit nonnegative rational honest norm bounds B')
    args = parser.parse_args()
    if any(norm < 0 for norm in args.norm):
        parser.error('norm bounds must be nonnegative')
    print(json.dumps([compare(norm) for norm in args.norm], indent=2))


if __name__ == '__main__':
    main()
