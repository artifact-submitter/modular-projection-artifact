#!/usr/bin/env bash
set -euo pipefail

# Build independent Lean modules in memory-aware batches.  The weight of a
# generated proof module is its number of `decide +kernel` declarations, which
# closely tracks retained reduction state for the balanced-ternary replay.

if (($# < 3)); then
  echo "usage: $0 MAX_TARGETS MAX_WEIGHT TARGET..." >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

max_targets=$1
max_weight=$2
shift 2

if ! [[ "$max_targets" =~ ^[1-9][0-9]*$ ]]; then
  echo "maximum target count must be a positive integer" >&2
  exit 2
fi
if ! [[ "$max_weight" =~ ^[1-9][0-9]*$ ]]; then
  echo "maximum batch weight must be a positive integer" >&2
  exit 2
fi

export LEAN_GC_THRESHOLD=${LEAN_GC_THRESHOLD:-256}

weighted=()
for target in "$@"; do
  source=${target//./\/}.lean
  weight=1
  if [[ -f "$source" ]]; then
    count=$(grep -c 'decide +kernel' "$source" || true)
    if ((count > 0)); then
      weight=$count
    fi
  fi
  weighted+=("$(printf '%09d|%s' "$weight" "$target")")
done

sorted=()
while IFS= read -r item; do
  sorted+=("$item")
done < <(printf '%s\n' "${weighted[@]}" | sort -r)

batch=()
batch_weight=0
built=0
total=${#sorted[@]}

flush_batch() {
  if ((${#batch[@]} == 0)); then
    return
  fi
  printf 'Building %d targets (weight %d; completed %d of %d)\n' \
    "${#batch[@]}" "$batch_weight" "$built" "$total"
  lake build "${batch[@]}"
  built=$((built + ${#batch[@]}))
  batch=()
  batch_weight=0
}

for item in "${sorted[@]}"; do
  weight_text=${item%%|*}
  target=${item#*|}
  weight=$((10#$weight_text))
  if ((${#batch[@]} > 0 &&
      (${#batch[@]} >= max_targets || batch_weight + weight > max_weight))); then
    flush_batch
  fi
  batch+=("$target")
  batch_weight=$((batch_weight + weight))
done
flush_batch
