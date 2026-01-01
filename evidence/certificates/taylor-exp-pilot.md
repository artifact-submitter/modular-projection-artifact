# Taylor exponential pilot

This tests the exponential-enclosure proposal supplied on 2026-09-12.
It is a proved arithmetic alternative, **not a production migration**.
No public probability bound or active certificate provider changes.

## Proof

For nonnegative `t`, the degree-four Taylor polynomial `P4(t)` is at most
`exp(t)`. Hence its reciprocal bounds `exp(-t)` from above. The evaluator
computes `P4` by outward-rounded interval Horner arithmetic, clamps its lower
endpoint to one (a proved lower bound), takes the reciprocal, and squares
`k` times for `t = x / 2^k`. This negative branch needs only `x ≥ 0`.

For `0 ≤ t ≤ 1`, Mathlib's explicit remainder bound gives
`exp(t) ≤ P4(t) + t^5/100`. The positive branch evaluates this polynomial and
squares it; it requires `0 ≤ x ≤ 2^k`. Both containment theorems compile and
pass the standard-only axiom canary. Small exact tests check zero and compare
positive and negative endpoints with the original evaluator.

Independent read-only review found no mathematical or trust issues. Its
documentation-only row-interval qualification is reflected below.

## Measured scope

All measurements use Lean 4.33.1, `decide +kernel`, the same workstation and
compiled dependencies. The second pair reverses execution order. CPU means
the process's reported user CPU, not elapsed kernel-phase time.

| Exact check | Legacy CPU, pair 1 / 2 | Taylor CPU, pair 1 / 2 |
| --- | ---: | ---: |
| 128 negative exponentials, 512 bits | 24.06 / 21.21 s | 2.67 / 2.74 s |
| First 200 upper-contour cells, unchanged raw upper endpoints | 43.13 / 35.93 s | 32.78 / 33.15 s |

The isolated arguments are `90*i/127` for `i = 0,...,127`, using 24 original
squarings versus 10 Taylor squarings. Both lists of exact outputs were
kernel-checked. Every Taylor upper endpoint is no larger than its original
counterpart; 127 are strictly smaller, with equality at zero.

The full-cell pilot changes the Gaussian-weight exponential and orders the
row interval for arbitrary inputs. On the catalogued profile boxes that
interval is unchanged, since its upper endpoint is nonnegative.
All eight 25-cell sums pass their original
frozen upper endpoints. The measured saving falls to **8–24% CPU**, so the
isolated 7.7–9.0-fold speedup is not a whole-certificate claim. Most of the
real shard's work remains outside this exponential call. Machine load and
CPU-time variation make the smaller observed saving particularly important.

The experimental cell evaluator still needs its containment bridge and
production wiring before it can replace active replay. Those changes are
lower priority than removing rectangles or sharing duplicated cap checks.
No full-family replay or timing was performed.

## Reproduction

`scripts/GenerateTaylorExpBench.lean legacy|taylor` emits the isolated fixture;
`scripts/GenerateUpperTaylorBench.lean legacy|taylor` emits the matched
200-cell fixture. Run either with `lake env lean --run`, save its output to
a temporary Lean file, then check that file with
`/usr/bin/time -p lake env lean -j1 --profile`. Generation is untrusted;
the emitted theorems establish their results only after kernel checking.
