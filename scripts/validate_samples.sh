#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"
source "$PROJECT_ROOT/scripts/validation_environment.sh"

python3 -c 'import tomllib' 2>/dev/null || {
  echo "Python 3.11 or newer is required for TOML validation." >&2
  exit 1
}

python3 scripts/check_dependency_cache.py
python3 scripts/check_certificate_catalog.py
python3 scripts/test_sample_selection.py
python3 scripts/test_compute_sample_cache_key.py
python3 scripts/run_certificate_samples.py "$@"

echo "Certificate sample validation passed."
