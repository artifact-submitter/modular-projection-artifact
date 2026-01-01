#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"

# Exact dyadic shard replay is deliberately bounded by LEAN_NUM_THREADS.  A
# single Lake scheduler can own the complete target set while running at most
# that many expensive kernel checks concurrently. Successful targets remain
# cached if a later target fails, so this script is safely resumable.
BATCH_SIZE=${CERTIFIEDJL_SPARSE_UPPER_CONTOUR_BATCH_SIZE:-all}
families=(
  Rows192Bits128Threshold287
  Rows256Bits152Threshold365
  Rows256Bits192Threshold406
  Rows384Bits192Threshold509
  Rows512Bits256Threshold681
)

targets=()
certificate_targets=()
for family in "${families[@]}"; do
  replay_root="CertifiedJL/Certificates/Families/L2Upper/ContourFamily/Replay/$family"
  family_target_count=0
  while IFS= read -r source; do
    module=${source%.lean}
    targets+=("${module//\//.}")
    family_target_count=$((family_target_count + 1))
  done < <(find "$replay_root" -name 'Shard*.lean' -type f | LC_ALL=C sort)

  if [[ ${1:-} != --list-targets ]]; then
    echo "# Queued $family ($family_target_count exact kernel shards)"
  fi
  certificate_targets+=(
    "CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.$family.Certificate"
  )
done

if [[ ${1:-} == --list-targets ]]; then
  printf '%s\n' "${targets[@]}"
  exit 0
fi

echo "# Replaying ${#targets[@]} balanced-ternary contour-family kernel shards"
./scripts/build_targets_in_batches.sh "$BATCH_SIZE" "${targets[@]}"
lake build "${certificate_targets[@]}"
