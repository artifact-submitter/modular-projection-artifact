#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"
source "$repo_root/scripts/validation_environment.sh"

python_bin=python3
if ! "$python_bin" -c 'import tomllib' 2>/dev/null; then
  for candidate in python3.13 python3.12 python3.11; do
    if command -v "$candidate" >/dev/null 2>&1; then
      python_bin=$candidate
      break
    fi
  done
fi
"$python_bin" -c 'import tomllib' 2>/dev/null || {
  echo "Python 3.11 or newer is required for native replay validation." >&2
  exit 1
}

"$python_bin" scripts/check_dependency_cache.py
"$python_bin" scripts/check_certificate_catalog.py
"$python_bin" scripts/check_replay_families.py
"$python_bin" scripts/check_public_catalogs.py
"$python_bin" scripts/check_contract.py
"$python_bin" scripts/check_certificate_workflow.py
"$python_bin" scripts/check_trust.py
"$python_bin" scripts/check_fast_import_boundary.py
"$python_bin" scripts/test_native_shadow_replay.py

plan_only=false
for argument in "$@"; do
  if [[ "$argument" == "--plan-only" ]]; then
    plan_only=true
  fi
done

runtime_dir=${CERTIFIEDJL_NATIVE_BUILD_DIR:-}
if [[ -z "$runtime_dir" ]]; then
  runtime_dir=$(mktemp -d "${TMPDIR:-/tmp}/certifiedjl-native-replay.XXXXXX")
  export CERTIFIEDJL_NATIVE_BUILD_DIR="$runtime_dir"
fi
if [[ -z "${CERTIFIEDJL_NATIVE_SHADOW_DIR:-}" ]]; then
  export CERTIFIEDJL_NATIVE_SHADOW_DIR="$runtime_dir"
fi

"$python_bin" scripts/native_shadow_replay.py "$@"
if [[ "$plan_only" == true ]]; then
  echo "native replay plan retained at $runtime_dir"
  exit 0
fi
"$python_bin" scripts/audit_native_replay.py --runtime-dir "$runtime_dir"
"$python_bin" scripts/native_shadow_replay.py \
  --runtime-dir "$runtime_dir" --finalize-receipt
echo "native replay evidence retained at $runtime_dir"
