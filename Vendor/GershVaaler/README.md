# Gersh Vaaler source snapshot

This directory contains the Vaaler–Beurling Fourier-analysis modules that
CertifiedJL uses to prove its Prawitz smoothing inequality.

## Provenance

- Upstream repository:
  [gersh/ternary-goldbach-lean](https://github.com/gersh/ternary-goldbach-lean)
- Upstream revision:
  `89416190c037331d7ebc04cd62ddb974cfb4dfcf`
- Upstream copyright: Gershon Bialer, 2026
- License: Apache License 2.0

Each copied Lean file retains its upstream copyright and license header and
carries a prominent CertifiedJL modification notice. CertifiedJL’s root
[`NOTICE`](../../NOTICE) records the attribution and scope of the changes.

## Adaptations

CertifiedJL made the following scoped changes:

- moved upstream `MathExtras` and `ext/analytic_nt/AnalyticNT` modules below
  the `Vendor.GershVaaler` import root;
- rewrote local imports to match that root;
- removed diagnostic `#print axioms` commands;
- applied small elaboration and tactic compatibility changes for Lean 4.31
  and CertifiedJL’s pinned Mathlib revision;
- replaced the upstream `VaalerInterpolationLower` dependency in
  `MathExtras/NumberTheory/Analysis/VaalerGPoUReprDecay.lean` with a local
  elementary proof of `posTail_sq_ge` from the already imported
  `two_inv_le_aux`.

The last change prunes unrelated large-sieve material; it does not add a
mathematical assumption. The copied snapshot contains no `sorry`, project
axiom, `unsafe` declaration, or compiler-backed decision proof.

## Verification

From the CertifiedJL repository root, run:

```bash
python3 scripts/check_trust.py
lake build
```

The first command scans both `CertifiedJL/` and `Vendor/` for forbidden trust
shortcuts. The second command kernel-checks the vendored modules that occur in
the production import closure.

To audit the snapshot against upstream, check out the recorded revision,
compare upstream `MathExtras/` and `ext/analytic_nt/AnalyticNT/` with this
directory after normalizing import prefixes, and inspect the compatibility
changes described above.
