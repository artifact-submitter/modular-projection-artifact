# Shorter upper-contour certificates with the same bounds

The legacy 512-row, 192-bit, strict threshold-607 result now uses earlier
analytic Gaussian tails. This removes 6,025 of its 8,000 rectangle checks.
The public probability theorem, all ten low-profile targets, and the
high-profile endpoint are unchanged.

## Proof structure

`ShortTail.tail_integral_le` generalizes the existing tail argument from
cutoff 8 to any positive rational cutoff. Beyond the cutoff, the row
majorant is bounded by its real-axis cap. The Gaussian quadrature tail
then has the closed bound already proved by
`integral_Ioi_gaussianQuadratureWeight_le`.

`ShortTail.integral_le` combines that tail with a finite initial rectangle
sum. It requires exact coverage of the retained cells. `endpoint_lt` also
requires proved chunk endpoints and a strict numeric budget check; stored
raw totals alone are not accepted as proof.

The internal `SparseL2UpperContour512Bits192` contract now states the actual
scaled contour integral bound on every profile box. Previously it stated
the output of the fixed 800-cell evaluator. Verified and Fast providers
still share exactly one named contract, and `normalized607_of_contract`
derives the same strict probability theorem. The contract contains no
final-probability assumption and no new trust primitive.

## Exact retained geometry

| Box | Retained chunks | Cutoff | Original target |
| --- | ---: | ---: | ---: |
| 00 | 15 | 15/4 | 97/100 |
| 01 | 12 | 3 | 99/100 |
| 02 | 10 | 5/2 | 99/100 |
| 03 | 9 | 9/4 | 49/50 |
| 04 | 8 | 2 | 99/100 |
| 05 | 7 | 7/4 | 19/20 |
| 06 | 6 | 3/2 | 99/100 |
| 07 | 5 | 5/4 | 3/4 |
| 08 | 4 | 1 | 3/5 |
| 09 | 3 | 3/4 | 3/5 |

Each chunk contains 25 cells with mesh 1/100. The total is 79 chunks and
1,975 cells, compared with 320 chunks and 8,000 cells previously.

## Reproduction and validation boundary

Run `python3 scripts/generate_upper_short_tail.py --check` to compare the
25 generated files with their source. The generator copies only the retained
original chunk statements and proofs, preserving every exact interval. It
does not claim or establish correctness of the raw endpoints by itself.
The original raw data remains available. The 51 superseded legacy replay
modules have been deleted; the shortened generator derives its proof leaves
directly from the retained raw data, without the old replay as an input.
The separate opt-in closed-core experiment is not a legacy replay dependency.

Validation performed during development:

- Kernel-checked generic tail, finite-prefix coverage consumer, endpoint
  soundness, and final strict probability consumer.
- Kernel-checked all ten unchanged budgets against the new numeric function.
- Two registered retained-prefix identities: Box00/Shard00 (200 cells) and
  Box09/Shard00 (75 cells). Both passed; the complete Box09 endpoint also passed.
- Generator roundtrip, 79-chunk structural regression, catalog, replay-family,
  and Fast import-boundary checks passed.
- The lightweight Fast canary checks the new theorems' standard-only axiom
  footprints without importing expensive retained-prefix replay.
- `./scripts/validate.sh fast` passed after integration (67 boundaries,
  96 public results, 291 supported declarations, and 16 Fast roots).

Independent review found no blocking mathematical, trust, or contract-wiring
issues. During that review, an unintended production-result build also
completed Box02/Shard01 and Box03/Shard01 before it was stopped. This exceeded
the intended two-sample development scope; these are incidental checks, not
new registered samples or a complete replay. No build process was left running.

No complete kernel or native replay was run. The reduction is an exact
source/dependency work count, not a full-family elapsed-time measurement,
and it does not upgrade the result's release-evidence class. Closed Gaussian
core alternatives remain a separate workstream.
