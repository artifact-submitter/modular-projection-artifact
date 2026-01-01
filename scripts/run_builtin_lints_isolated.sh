#!/usr/bin/env bash
set -euo pipefail

if (($# == 0)); then
  echo "usage: $0 MODULE..." >&2
  exit 2
fi

for module in "$@"; do
  lake lint --builtin-only "$module"
done
