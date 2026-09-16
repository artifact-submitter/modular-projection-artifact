# Review the proof artifact

You can inspect the source and verify the proof archive on any platform with
Python 3.11 or newer. To run the precompiled proofs and bundled tools, use Linux
x86-64. The validated system was Ubuntu 24.04. macOS and Windows cannot
directly run the bundled Linux executables; use a matching Linux environment
for those commands.

The source tag `validated-source-linux-amd64` points to commit
`dcb3f1e4792aaec07fc122ba96ce88b203f8e736`. Documentation on `main` may be
newer. The release receipt and the archive manifest bind the validated source,
compiled proofs, dependencies, and tools.

## Read the main statements

Start with these files. Each result refers to a named proposition whose
definition states its full assumptions and probability bound.

| Result | Lean file |
| --- | --- |
| Euclidean upper bound, constant 338 | [Rows256Bits128.lean](CertifiedJL/Results/L2/Upper/Rows256Bits128.lean) |
| Euclidean lower bound, constant 29 | [Rows256Bits128.lean](CertifiedJL/Results/L2/Lower/Rows256Bits128.lean) |
| Upper-bound proposition | [Upper.lean](CertifiedJL/Statements/L2/Upper.lean) |
| Lower-bound proposition | [Lower.lean](CertifiedJL/Statements/L2/Lower.lean) |

The bundle includes `Review.lean` and `theorem-map.json`, which connect the
cataloged results to declaration names and source files. The generated reviewer
file is a convenient selection of declarations; the full production kernel
replay covers every production module, including results outside that selection.

## Build the source natively on macOS or Linux

This path checks the source with your platform's Lean installation. Install
[Elan](https://github.com/leanprover/elan), then create a separate checkout at
the validated source tag:

```sh
git worktree add ../modular-projection-source validated-source-linux-amd64
cd ../modular-projection-source
lake update
lake build CertifiedJL
```

The checked-in `lean-toolchain` selects Lean 4.33.1, and
`lake-manifest.json` records the dependency revisions. Generate and check the
same reviewer selection used by the proof bundle:

```sh
python3 scripts/reviewer_workspace.py \
  --output .lake/native-reviewer-workspace
lake env lean .lake/native-reviewer-workspace/Review.lean
```

The final command prints the selected theorem types and axiom dependencies.
This native source build is useful for interactive inspection, but it is not a
replacement for the all-module release validation recorded in the bundle. Use
the Linux workflow below to reproduce that stronger check.

## Download, verify, and extract

Download the Linux proof archive and its checksum file from the
[release assets](https://github.com/artifact-submitter/modular-projection-artifact/releases).
Download every `proof-bundle-linux-amd64.tar.gz.part-*` file together with
`SHA256SUMS.parts` and `SHA256SUMS.bundle`. Check each downloaded part,
concatenate the parts in their numbered order, decompress the result, and then
check the reconstructed proof bundle:

```sh
sha256sum -c SHA256SUMS.parts
cat proof-bundle-linux-amd64.tar.gz.part-* | \
  gzip -dc > proof-bundle-linux-amd64.tar
sha256sum -c SHA256SUMS.bundle
```

Do not continue if a checksum fails. Compare the archive identity reported by
the verifier with the identity in the release notes. Internal hashes detect
changes but do not authenticate an unknown download by themselves.

From this repository's root, run the platform-independent archive verifier:

```sh
python3 scripts/proof_bundle.py verify \
  "$PWD/proof-bundle-linux-amd64.tar"
```

The command must print this bundle ID:

```text
sha256:6ebd2cd428cb11c99fb83501ae79e04dc3fb1291b6c4c54c922d38fd4ef09451
```

On Linux x86-64, also check the bundled toolchain against the host and extract
the archive into a directory that does not already exist:

```sh
python3 scripts/proof_bundle.py verify \
  --check-host-toolchain \
  --extract-to "$PWD/review-bundle" \
  "$PWD/proof-bundle-linux-amd64.tar"
```

The first command checks the archive members, validation receipt, and source and
build identities on any platform. The Linux command additionally checks the
platform and bundled runtime. Neither command requires an existing Lean
installation. Keep enough free space for both the archive and extracted files;
the release notes give the final sizes. Rebuilding requires additional space
for a second project build.

## Inspect the proofs in a terminal or VS Code

From the repository root after extraction:

```sh
cd review-bundle/source
export PATH="$(pwd)/../review-bin:$(pwd)/../toolchain/bin:$PATH"
../review-bin/lake --no-build env lean \
  .lake/release-reviewer-workspace/Review.lean
```

The command prints theorem types and axiom dependencies. It rejects axiom
dependencies outside `propext`, `Classical.choice`, and `Quot.sound`, the three
standard axioms permitted by this artifact. The bundled Lake wrapper resolves
dependencies locally and avoids dependency downloads.

For interactive inspection, install the Lean 4 extension in VS Code and open
`review-bundle/review.code-workspace`. Open
`source/.lake/release-reviewer-workspace/Review.lean` from that workspace.
The workspace selects the bundled tools and compiled dependencies. Follow a
theorem name to its declaration, then follow the named proposition to inspect
its hypotheses. For example, the following commands display the lower theorem
and its axiom dependencies in a file importing its result module:

```lean
import CertifiedJL.Results.L2.Lower.Rows256Bits128

#check CertifiedJL.Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29
#print axioms CertifiedJL.Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29
```

Use a separate scratch file for your own experiments. If VS Code proposes
installing another toolchain, check that you opened the supplied workspace on
Linux x86-64 and that the bundled tools are selected.

## Repeat fresh kernel checking

From `review-bundle/source`, run:

```sh
LEAN_NUM_THREADS=1 ../review-bin/lake --no-build env \
  leanchecker --fresh CertifiedJLReleaseAll
```

This checks the stored elaborated production proofs in a fresh kernel
environment. It does not rerun the tactics that constructed those proofs.
The checker uses Lean's kernel; the separate axiom inspection checks for
unexpected assumptions. Successful completion has exit status zero.

## Recompile and check all source modules

From the published repository root, choose three new destination directories:

```sh
python3 scripts/rebuild_frozen_bundle.py \
  --archive "$PWD/proof-bundle-linux-amd64.tar" \
  --bundle-dir "$PWD/rebuild/bundle" \
  --workspace "$PWD/rebuild/workspace" \
  --output-dir "$PWD/rebuild/result"
```

The adapter verifies and extracts the archive, starts with no project build,
compiles all classified production, Fast, test, and standalone-script modules,
checks the reviewer declarations, and performs fresh kernel replay. It uses the
bundled toolchain and verified dependency artifacts. The Fast library is checked
separately; its certificate assumptions do not enter the production proofs.

Successful output begins with `offline rebuild passed: sha256:`. Inspect
`rebuild/result/offline-rebuild-report.json` and its stage logs for your timings
and results. This report records a new reviewer run; the original release
receipt remains unchanged.

## Validated scope and measured resources

The successful Linux validation covered 1,959 production modules, 34 Fast
modules, 77 test modules, 10 standalone Lean scripts, and 94 reviewer
declarations. It checked that source, dependencies, and validation tools remained
unchanged throughout the run.

The machine had two CPUs, 16 GiB RAM, and 4 GiB swap. Lean used one thread.
Measured times were:

| Stage | Elapsed time |
| --- | --- |
| Production compilation | 3 h 33 min 9 s |
| Fresh kernel replay | 2 h 54 min 6 s |
| Complete validation, including other checks | 6 h 33 min 31 s |

Peak sampled process-tree memory was approximately 13.64 GiB. Allow several
hours for a complete rebuild; these measurements depend on the machine and
reuse verified dependency artifacts. Reading the source or opening the
precompiled proofs does not require repeating that build.
