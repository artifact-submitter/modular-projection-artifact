# Sparse upper certificate replays

The 256-row, 128-bit threshold-338 theorem uses the centered-hybrid replay.
Its low-profile branch covers
`sparseProfileFourthMoment ∈ [0, 1/20]` with 18 centered-hybrid boxes and
5,049 frequency cells through cutoff 8. The cells are aggregated into 523
exact chunks and 112 bounded replay shards. The complementary high-profile endpoint is a
small direct kernel arithmetic check, not a certificate assumption.

The certificate and analytic assembly prove the unconditional public theorem
`CertifiedJL.sparseUpper128` for 256 rows and failure probability below
`2⁻¹²⁸`.

## Pinned inputs

- Lean: `v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Generator: `scripts/generate_sparse_upper_hybrid.py`
- Exact arithmetic oracle:
  `paper/experiments/sparse-upper-centered-hybrid/verify_centered_hybrid.py`
- Generated dyadic precision: 320 bits
- Chunk size: 10 cells
- Replay shard size: 5 chunks

The Python oracle synthesizes untrusted dyadic endpoints. Lean recomputes each
chunk with kernel reduction, checks every cell-side condition, proves the
finite-integral aggregation, and then consumes the single semantic contract
`CertifiedJL.CertificateContracts.SparseL2UpperHybrid`.

## Reproduction

The deterministic nonwriting check is:

```sh
python3 scripts/generate_sparse_upper_hybrid.py --check
```

To regenerate and then verify that the committed tree is current:

```sh
python3 scripts/generate_sparse_upper_hybrid.py
python3 scripts/generate_sparse_upper_hybrid.py --check
git diff --exit-code -- \
  CertifiedJL/Certificates/Families/L2Upper/Rows256Bits128
```

Two bounded development samples are:

```sh
lake build CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box12.Shard00
lake build CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box17.Shard00
```

The complete kernel replay is:

```sh
lake build CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified
```

## 512 rows, 192 bits, threshold 607

The higher-security theorem uses the shifted-Gaussian contour. Ten adjacent
profile boxes cover `[0,1/20]`. The preserved raw payload has 800 frequency
cells per box at mesh `1/100`; the active short-tail proof recomputes only 79
chunks of 25 cells, or 1,975 cells total, in 14 bounded replay shards. Earlier
analytic Gaussian tails cover the discarded suffixes without changing any
box target. The complementary profile range uses a standalone real-axis
endpoint at the same 512-bit precision. That precision is material: at 384 bits the enclosure of
`exp (-353881/1000)` rounds up to one dyadic unit before multiplication and
cannot certify the final strict comparison.

The exact flat-vector frontier audit is:

```sh
python3 paper/artifact/upper-gap/verify_high_security_upper_obstructions.py
```

This raw exact-arithmetic checker covers the four finite flat witnesses
`(rows,bits,threshold) = (256,192,404)`, `(384,192,507)`,
`(512,192,605)`, and `(512,256,678)`. Lean independently checks their Gamma
floors in `HighSecurityUpperGamma`, their even-dimensional radial identities,
their mesh/truncation inequalities, and their final strict finite events.
These proofs contain no generated Lean leaf data and no fast assumption, so
they do not create a `public-results.toml` semantic-assumption boundary or a
bounded generated-leaf sample. `ObstructionCanariesFast` is the deterministic
development root for all four literal public theorem types and axiom
footprints.

In particular, the 512-row, 192-bit witness rules out threshold 605. The
matched-Gamma benchmark at 606 is below budget, so the certified 607 endpoint
is within one integer of optimal and 606 remains open.

Regenerate or check the raw per-box payload and active short-tail replay with:

```sh
lake env lean --run scripts/GenerateSparseUpperContour.lean
lake env lean --run scripts/GenerateSparseUpperContour.lean --check
python3 scripts/generate_upper_short_tail.py
python3 scripts/generate_upper_short_tail.py --check
```

Two bounded samples and the complete replay are:

```sh
lake build CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Replay.Shards.Box00.Shard00
lake build CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Replay.Shards.Box09.Shard00
CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE=2 \
  ./scripts/build_sparse_upper_contour_proofs.sh
```

The helper first replays the independent high-profile endpoint, then
materializes the retained low-profile shard proofs before building the canonical
`CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Replay.Verified` root. It keeps no more
than two roughly 3.2 GiB shard elaborations live on the 16 GiB proof-record
runner.

## Trust boundary

Generated endpoints are data, not axioms. Production uses no `sorry`,
`admit`, project axiom, `unsafe`, or `native_decide`. The ordinary production
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The fast
library may replace only the named semantic contracts; each feeds the same
theorem assembly as its kernel-verified provider.
