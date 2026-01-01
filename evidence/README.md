# Evidence catalogs

This directory contains the machine-readable correspondence between the
mathematical result surface, Lean declarations, numerical certificates, and
the paper.

## Authoritative catalogs

- `result-catalog.toml` records every advertised mathematical result by row
  law, statistic, tail, exact parameters, failure budget, Lean declaration,
  verification class, certificate dependencies, and paper locator.
- `public-api.toml` is the intentional supported Lean API. It is short by
  design and does not inventory generated shards or every first-party name.
- `certificates/public-results.toml` records semantic certificate claims,
  verified and fast providers, data ownership, deterministic development
  samples, complete replay commands, and result consumers.
- `certificates/replay-families.toml` groups those claims by executable replay
  roots. It records mathematical replay topology, not CI scheduling or run
  history.
- `paper-snapshot.toml` pins the reviewed paper sources used for
  source-correspondence checks.
- `theorem-contract.toml` freezes the intentional main-result surface. It
  binds all advertised result records to their public canaries, certificate
  dependencies, and replay plan, and separately records checked or outstanding
  substantive negative claims. It does not inventory explanatory paper lemmas.

Generated operational inventories may live under `evidence/internal/`. They
are inputs to import-closure and release checks, not the public API.

## Interpretation

Read each result's `verification_class` before using it as release evidence.
Direct kernel elaboration and focused axiom checks can establish a theorem
without completing the repository's full proof-record replay. Such results
remain `replay_pending` until the required replay and attestation are complete.
Fast CI, partial family replays, and native runs do not establish
`kernel_checked` status.

`replay_pending` retains declaration-existence and exact statement checks.
It does not assert a completed native or kernel replay. Before promoting a
record, archive the successful full run and its emitted attestation with the
source commit, proof-closure digest, validation digest, Lean toolchain, mathlib
revision, and complete registered root/family counts. Verify the identities
against the source being advertised. A digest generated without the completed
replay is only an identity record, not evidence of proof completion.

`kernel_checked` means the exact Lean declaration exists without a project
assumption and its complete registered proof closure has passed the kernel
proof-record replay at the current source identity. `native_attested` means
the same production declaration and closure have passed exhaustive
compiler-trusted native replay, but the current closure has not yet passed the
full kernel proof-record replay. Fast assumed results retain the same analytic
assembly but are not assigned either class.
External-artifact and explicit-assumption records must identify their boundary
and must not be presented as kernel-checked results.

Source hashes establish identity and provenance. They are not mathematical
proofs. Certificate generators and independent audits remain outside the Lean
trust boundary; committed data become proof inputs only through proved Lean
checkers. Catalog validation nevertheless requires each repository-local
generator and each repository path named by a regeneration command to exist,
so the recorded reproduction instructions cannot silently decay.

The catalogs describe the current mathematical repository. Implementation
chronology and obsolete routes belong in version control history, not in these
records.
