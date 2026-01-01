#!/usr/bin/env bash
set -euo pipefail

# Build independent Lean targets in bounded Lake batches.  One Lake process
# owns each batch, so shared dependencies are replayed once per batch rather
# than once per target.  Lake keeps successful outputs when a later batch
# fails, making the command safely resumable.

if (($# < 2)); then
  echo "usage: $0 BATCH_SIZE|all TARGET..." >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

batch_size=$1
shift

# Keep the conservative heap policy used by the original memory-capped
# queues.  Callers can override it when benchmarking another machine.
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export LEAN_GC_THRESHOLD=${LEAN_GC_THRESHOLD:-256}

targets=("$@")
total=${#targets[@]}

if [[ "$batch_size" == all ]]; then
  # Lake itself honors LEAN_NUM_THREADS, so one scheduling invocation does not
  # increase the number of concurrently elaborated targets.  It only avoids
  # rediscovering the same build graph between tiny batches.
  batch_size=$total
elif ! [[ "$batch_size" =~ ^[1-9][0-9]*$ ]]; then
  echo "batch size must be a positive integer or 'all'" >&2
  exit 2
fi

for ((start = 0; start < total; start += batch_size)); do
  end=$((start + batch_size))
  if ((end > total)); then
    end=$total
  fi
  batch=("${targets[@]:start:end-start}")
  printf 'Building targets %d-%d of %d in one Lake process\n' \
    "$((start + 1))" "$end" "$total"
  lake build "${batch[@]}"
done
