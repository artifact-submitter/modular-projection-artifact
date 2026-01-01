#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"

mode=${1:-${CERTIFIEDJL_VALIDATION_MODE:-fast}}
if [[ $# -gt 0 ]]; then
  shift
fi

usage() {
  echo "usage: ./scripts/validate.sh [fast|samples [--base GIT_REV]|kernel|full --output-dir NEW_DIRECTORY|native [native-options...]]" >&2
}

case "$mode" in
  fast)
    if [[ $# -ne 0 ]]; then
      usage
      exit 2
    fi
    exec ./scripts/validate_fast.sh
    ;;
  samples)
    exec ./scripts/validate_samples.sh "$@"
    ;;
  native)
    exec ./scripts/validate_native.sh "$@"
    ;;
  full)
    if [[ $# -lt 2 || "$1" != "--output-dir" ]]; then
      usage
      exit 2
    fi
    exec python3 scripts/release_validation.py run "$@"
    ;;
  kernel)
    if [[ $# -ne 0 ]]; then
      usage
      exit 2
    fi
    exec ./scripts/validate_certificates.sh
    ;;
  *)
    echo "unknown validation mode: $mode" >&2
    usage
    exit 2
    ;;
esac
