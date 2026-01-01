#!/usr/bin/env bash
set -euo pipefail

# Materialize the active 512-row short-tail shards before Lake sees the
# aggregate import graph.  Lake's worker pool remains bounded by
# LEAN_NUM_THREADS; using one scheduling invocation avoids repeated graph
# discovery without increasing concurrent exact-arithmetic elaboration.

repo_root=$(cd "$(dirname "$0")/.." && pwd)
batch_size=${CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE:-all}

if [[ "$batch_size" != all ]] && ! [[ "$batch_size" =~ ^[1-9][0-9]*$ ]]; then
  echo "CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE must be a positive integer or 'all'" >&2
  exit 2
fi

targets=()
shard_counts=(2 2 2 2 1 1 1 1 1 1)
for box_index in $(seq 0 9); do
  for shard_index in $(seq 0 $((${shard_counts[$box_index]} - 1))); do
    targets+=(
      "CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Replay.Shards.Box$(printf '%02d' "$box_index").Shard$(printf '%02d' "$shard_index")"
    )
  done
done

if [[ ${1:-} == --list-targets ]]; then
  printf '%s\n' "${targets[@]}"
  exit 0
fi

lake build CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.HighProfile
"$repo_root/scripts/build_targets_in_batches.sh" "$batch_size" "${targets[@]}"
lake build CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Replay.Verified
