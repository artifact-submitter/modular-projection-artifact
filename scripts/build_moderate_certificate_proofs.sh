#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
batch_size=${CERTIFIEDJL_MODERATE_BATCH_SIZE:-${CERTIFIEDJL_MODERATE_JOBS:-2}}

if ! [[ "$batch_size" =~ ^[1-9][0-9]*$ ]]; then
  echo "CERTIFIEDJL_MODERATE_BATCH_SIZE must be a positive integer" >&2
  exit 2
fi

cd "$repo_root"
cell_count=24
targets=()
for cell_index in $(seq 0 "$((cell_count - 1))"); do
  targets+=(
    "CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell$(printf '%03d' "$cell_index")"
  )
done

"$repo_root/scripts/build_targets_in_batches.sh" "$batch_size" "${targets[@]}"

# Materialize the checked aggregate so later library closure only imports it.
lake build CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.TheoremAssembly
