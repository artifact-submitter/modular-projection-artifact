# Closed Tyurin core across the switch

Base: `withheld-for-anonymous-review`.

The remaining four core meshes are replaced by one quadratic density envelope.
For cutoff `T`, choose

`c = max(upper(L^(2/3)), 2 L T / 5 + 25 / (27 T²))`.

On the post-switch branch `L s³ ≥ 125/27`, the inequality
`L s³/5 + 25/54 ≤ c s²/2` follows by multiplying through by the positive
`T²` and factoring the difference as
`(T-s) [54 L T² s² - 125(T+s)]` (up to the positive scale).
The bracket is nonnegative because `s ≤ T` and `54 L s³ ≥ 250`.
On the first branch, the variance-cap term in `c` suffices.

The unified-density integral then reduces both branches to the already-proved
quadratic Gaussian moment bound. No core quadrature remains in any of the 24
production cells. This phase removes the last 24 core chunk proofs and 1,200
core rectangles, retaining the exact outer chunks, targets, and `CellCertified`
provider type.

Four constant-size exact budget checks passed together in 0.515 seconds of
kernel checking. Preliminary floating scaled budget/target ratios were
0.9535922, 0.9624231, 0.9735094, and 0.9872570; the Lean checks use the exact
rational arithmetic and do not rely on these diagnostics.

## Paired production Cell023 measurement

Both invocations used `lake env lean -j1 --profile` and `/usr/bin/time -p`.

| Whole Cell023 | Profiler type checking | Wall | User |
| --- | ---: | ---: | ---: |
| Original six core + five outer chunks | 157 s | 174.55 s | 55.08 s |
| Closed crossing core + same five outer chunks | 45.4 s | 61.71 s | 14.30 s |

The six removed core checks account for 117.2 seconds of the baseline profiler
total. User CPU time fell 74.0%; profiler checking fell 71.1%. Concurrent machine
load affects elapsed profiler and wall times; no complete-grid timing is
extrapolated. Both production invocations exited successfully.

The fast replay-alternative canary now imports and checks the crossing-core
soundness theorem, same-provider bridge, and exact four-cell budgets. Production
trust scan and certificate catalog validation pass. No new axiom, unsafe code,
native production replay, or weaker public bound was introduced. Full replay is
not part of this bounded experiment. No Tyurin outer work was attempted: the
user redirected the next mathematical effort to upper contours.
