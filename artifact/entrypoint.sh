#!/bin/sh
set -eu

archive=${CERTIFIEDJL_PROOF_BUNDLE:-/artifact/proof-bundle.tar}
workspace=${CERTIFIEDJL_WORKSPACE:-/workspace/proof-bundle}

if [ ! -f "$archive" ]; then
  echo "missing proof archive: $archive" >&2
  exit 2
fi
if [ -e "$workspace" ]; then
  echo "workspace must be a fresh path: $workspace" >&2
  exit 2
fi

PYTHONPATH=/opt/certifiedjl/scripts \
python3 /opt/certifiedjl/scripts/proof_bundle.py verify \
  --check-host-toolchain --extract-to "$workspace" "$archive"

export PATH="$workspace/review-bin:$workspace/toolchain/bin:$PATH"
if [ "$#" -gt 0 ]; then
  exec "$@"
fi

cd "$workspace/source"
exec "$workspace/review-bin/lake" env lean \
  -R "$workspace" "$workspace/Review.lean"
