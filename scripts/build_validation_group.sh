#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 GROUP" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

group=$1
batch_size=$(python3 scripts/validation_roots.py "$group" --batch-size)
targets=()
while IFS= read -r target; do
  targets+=("$target")
done < <(python3 scripts/validation_roots.py "$group")

if ((${#targets[@]} == 0)); then
  echo "$group: validation group has no targets" >&2
  exit 1
fi

python3 scripts/validation_roots.py "$group" --describe
exec ./scripts/build_targets_in_batches.sh "$batch_size" "${targets[@]}"
