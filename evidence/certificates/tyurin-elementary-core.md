# Elementary Tyurin core: retained proof and historical measurement

The closed-core proof preserves all 24 published Lyapunov cells and the strict
`3/5` target. Convexity bounds the eight-trapezoid quadratic sum by its exact
second/fourth moments. The Gaussian moment is integrated over the positive
half-line. `Probability.tyurinCoreIntegral_le_closed` bounds the actual Prawitz
kernel/discrepancy integral without core quadrature hypotheses.

The first 20 cells use this pre-switch bound. The final four now use the
crossing-core theorem; all 24 use the scaled outer plan. See
[the crossing-core record](tyurin-crossing-core.md) and
[current scalability documentation](../../docs/certificate-scalability.md).

## Historical paired measurement

Against base `withheld-for-anonymous-review`, the first production
cell was checked with matching direct Lean commands:

| Whole Cell000 scope | Kernel type checking | Wall | User |
| --- | ---: | ---: | ---: |
| Six core plus five outer chunks | 42.7 s | 45.66 s | 41.33 s |
| Closed core plus five outer chunks | 9.89 s | 23.62 s | 10.71 s |

The 76.8% checking reduction concerns this historical sample, not the current
whole family. The later scaled outer plan supersedes its five outer chunks.
No full-grid timing is inferred.

## Cleanup and trust

The intermediate chord prototypes, stored legacy chunk totals, old data
generator, and orphaned certificate-data assembly were removed at closeout.
Their historical sources remain in Git. The active generator is
`scripts/generate_moderate_certificate_proofs.sh`; regeneration no longer
computes obsolete totals. Mutation canaries now reject a zero-sized active
outer plan rather than mutate a discarded core certificate.

The generic analytic proofs and active same-`CellCertified` assembly remain
covered by the standard-only axiom canary. Arithmetic replay uses
`decide +kernel`, with no native replay, production axioms, `sorry`, or unsafe
declarations. Full replay was not run during this optimization pass.
