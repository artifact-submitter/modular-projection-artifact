# Experimental closed upper-contour core

## Proved, but not production-wired

The signed row argument retains cancellation and bounds the actual row
majorant by `exp(-(103/100)*u^2)` for profiles in `[0,1/1024]` and
frequencies in `[0,1/4]`. Raising to 512 rows, including the contour weight,
and integrating a half-Gaussian bounds the core integral by `1669/25000`.
The suffix uses 140 cells of mesh `1/40`, indices 10 through 149, and the
tail begins at `15/4`. The original prefactor and strict `97/100` target
are unchanged; the checked interval endpoint is approximately 0.9696038471.

The complete semantic endpoint was kernel-checked in worker commit
`withheld-for-anonymous-review`. Independent review of the signed core and final mesh/assembly
found no mathematical or trust issues. In particular, the three intervals
cover `Ioi 0` without gaps or double-counted endpoints, and the final
prefactor inequality uses nonnegativity of the actual integral.

Commit `withheld-for-anonymous-review` separates the numerical provider into
`Rows512Bits192/Replay/ClosedCoreFirstBox.lean`. The same endpoint in
soundness now takes the named numerical budget as a hypothesis. Both
analytic modules recompiled after this split; the relocated numerical
provider was not replayed again. Its unchanged numerical proof had already
been checked before the split. Production continues to use ShortTail;
the retired/experimental `Rows512Bits192.Replay` namespace is barred from
Fast, which checks only the analytic lemmas and conditional endpoint.

## Cost evidence

This first box needs 140 rather than 375 rectangle evaluations, a structural
62.7% reduction. There is no matched full first-box runtime comparison.
The worker's clean build of the original combined endpoint module took
46.53 seconds wall and 51.45 seconds user CPU with its imported core already
available. After the split, a core-module run took 26.81 seconds wall and
20.06 seconds user CPU; first-box soundness runs took 19.82/13.79 and
5.69/11.79 seconds wall/user CPU. These are different build scopes with
cache and concurrency effects, not additive or directly comparable totals.
They do not establish a net production gain.

The 140-cell experiment tests a distinct same-bound proof strategy; it is
not a full family replay. The production sample list is unchanged. Before
production migration, split the numerical work into bounded registered
leaves and compare total cost including the analytic modules.

## Larger-root follow-through

The Astra-low follow-up exported the generic signed-modulus lemma and
examined hybrid 256/128/threshold-338 box zero (`lambda=5/8`, profiles
`[0,1/4096]`). A proposed `exp(-(7/5)*u^2)` envelope passed outward-rounded
320-bit point checks at both profile endpoints and 100 positive frequencies
`u=i/400`. This is only sampling, not a continuous Lean proof. The maximum
sample ratio was approximately 0.9999976391; exponent `13/10` also passed.

Reproduction uses `BASE` from
`paper/experiments/sparse-upper-centered-hybrid/verify_centered_hybrid.py`,
its `row_expression_on_cell(p,u,u,Fraction(5,8))`, the positive exponential
enclosure at `(7/5)*u*u` with scaling 24, and the integer comparison
`row.hi * exp.hi <= SCALE**2`.

At that experiment's baseline, only 55 of the root's 6,554 cells lay in this
first-box core: 0.84%. The later production hybrid pass reduces the family
to 5,049 cells through an earlier tail and coarser high-profile meshes.
The parameterized signed envelope and Gaussian integral assembly now compile,
with exact row witnesses for two generalized 384-row boxes; they are not yet
production-wired. See [the closeout record](../../docs/upper-contour-reduction-progress.md).
