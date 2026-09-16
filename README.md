# Modular projection proof artifact

This repository contains the Lean formalization accompanying the paper on
modular Johnson–Lindenstrauss projection bounds. It includes upper and lower
tail bounds, numerical certificates, and counterexamples to stronger claims.

Start with [the reviewer guide](REVIEWING.md). You can read the theorem
statements directly, inspect their types and axioms in VS Code using the
precompiled Linux bundle, or repeat the full compilation and kernel checks.
The guide explains the download and verification procedure; release assets
and checksums are listed on the
[releases page](https://github.com/artifact-submitter/modular-projection-artifact/releases).

The tag `validated-source-linux-amd64` identifies the exact anonymous source
used for the successful Linux validation. Its commit is
`dcb3f1e4792aaec07fc122ba96ce88b203f8e736`. Documentation may be added to
`main` without changing that validated source. The bundle's receipt identifies
the compiled source and the checks performed.

The precompiled distribution targets Linux x86-64 and includes Lean 4.33.1,
dependencies, and validation evidence. First-party author metadata was
anonymized before compilation; mathematical Lean code and third-party
attribution were preserved. Matching publicly available code can still reveal
provenance.
