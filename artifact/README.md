# CertifiedJL anonymous proof-bundle container

The container is a convenience wrapper around a frozen anonymous proof archive.
The archive remains authoritative. It contains the receipt-bound Lean sources,
reusable build artifacts, exact dependency trees, validation evidence, and
matching Lean `bin/` and `lib/` runtime trees.

The entry point verifies every archive member, checks the host platform and
bundled runtime, extracts into a new directory, and elaborates the generated
reviewer file. These container files define a workflow; they do not claim that a
particular image or complete release run has passed.

## Prerequisites

Use an anonymous bundle produced before compilation from a separate neutral
source tree. Do not mount an identified checkout into the reviewer container.

The Dockerfile has no default base image. Set `BASE_IMAGE` to an immutable,
digest-pinned Linux image that contains a compatible Linux userspace and Python
3.11 or newer. It does not need Lean, Lake, Elan, Git, or network access. A blank
value or tag-only image reference is not a reproducibility claim.

## Build and run

Build from the repository root:

```sh
docker build \
  --build-arg BASE_IMAGE="$CERTIFIEDJL_BASE_IMAGE" \
  -f artifact/Dockerfile \
  -t certifiedjl-proof .
```

Run a Linux/x86_64 bundle only on a matching Linux/x86_64 userspace:

```sh
docker run --rm \
  -v "$PWD/proof-bundle.tar:/artifact/proof-bundle.tar:ro" \
  certifiedjl-proof
```

The default command verifies and extracts the archive, then checks
`Review.lean`. A successful exit establishes that this inspection command
passed. It does not replace the anonymous release receipt inside the archive.

To run another non-building inspection command, pass it after the image name:

```sh
docker run --rm \
  -v "$PWD/proof-bundle.tar:/artifact/proof-bundle.tar:ro" \
  certifiedjl-proof \
  sh -lc 'cd /workspace/proof-bundle/source && \
    ../review-bin/lake --no-build env lean \
    .lake/release-reviewer-workspace/Review.lean'
```

The entry point verifies and extracts the archive before executing the supplied
command. It prepends `review-bin` and `toolchain/bin` to `PATH`.

## Use VS Code or a dev container

Open `review.code-workspace` from the extracted archive. It selects `source/`,
prepends the bundle-local Lake wrapper and bundled toolchain, disables automatic
dependency builds, and requires confirmation before any toolchain installation.

`review-bin/lake` invokes the shipped Lake executable with the bound
`source/.lake/release-package-overrides.json`. The override resolves Git-free
dependencies under `source/.lake/packages/` as local paths. It does not rewrite
the frozen project manifest or contact the recorded dependency URLs.

For the dev-container configuration, set both host environment variables before
opening the repository in its container:

```sh
export CERTIFIEDJL_BASE_IMAGE='registry.example/python@sha256:<digest>'
export CERTIFIEDJL_PROOF_BUNDLE='/absolute/path/proof-bundle.tar'
```

The dev container mounts the archive read-only. Its image entry point performs
verification and extraction before VS Code attaches, and its workspace folder is
`/workspace/proof-bundle/source`.

## Rebuild all source modules

Do not use an umbrella `lake build` command as evidence of an authoritative
release. To rebuild every classified source module, run the explicit offline
adapter from a published checkout:

```sh
python3 scripts/rebuild_frozen_bundle.py \
  --archive /absolute/path/proof-bundle.tar \
  --bundle-dir /tmp/certifiedjl-rebuild/bundle \
  --workspace /tmp/certifiedjl-rebuild/workspace \
  --output-dir /tmp/certifiedjl-rebuild/result
```

Each destination must be new. The adapter verifies and extracts the bundle,
starts with an absent project build directory, rebuilds all classified source
classes, regenerates the reviewer and production import root, and performs a
fresh kernel replay. It reuses the bundle's verified dependency artifacts.

The resulting `offline-rebuild-report.json` explicitly states
`authoritative_release_receipt: false`. It is additional reviewer evidence, not
a replacement for the original anonymous cold-validation receipt.

See [Anonymous submission artifact](../docs/submission-artifact.md) for source
preparation, freeze-pointer, manuscript-review, and submission-composition rules.
