#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"
source "$PROJECT_ROOT/scripts/validation_environment.sh"

PYTHON_BIN="python3"
if ! "$PYTHON_BIN" -c 'import tomllib' 2>/dev/null; then
  for candidate in python3.13 python3.12 python3.11; do
    if command -v "$candidate" >/dev/null 2>&1; then
      PYTHON_BIN="$candidate"
      break
    fi
  done
fi
"$PYTHON_BIN" -c 'import tomllib' 2>/dev/null || {
  echo "Python 3.11 or newer is required for TOML validation." >&2
  exit 1
}

"$PYTHON_BIN" scripts/check_dependency_cache.py
"$PYTHON_BIN" scripts/check_certificate_catalog.py
"$PYTHON_BIN" scripts/test_check_certificate_catalog.py
"$PYTHON_BIN" scripts/check_replay_families.py
"$PYTHON_BIN" scripts/test_check_replay_families.py
"$PYTHON_BIN" scripts/check_public_catalogs.py
"$PYTHON_BIN" scripts/check_counterexample_catalog.py
"$PYTHON_BIN" scripts/test_counterexample_catalog.py
"$PYTHON_BIN" scripts/test_counterexample_probability.py
"$PYTHON_BIN" scripts/check_counterexample_searches.py
"$PYTHON_BIN" scripts/test_search_counterexamples.py
"$PYTHON_BIN" scripts/render_counterexample_coverage.py --check
"$PYTHON_BIN" scripts/test_counterexample_coverage.py
"$PYTHON_BIN" scripts/check_contract.py
"$PYTHON_BIN" scripts/test_check_contract.py
"$PYTHON_BIN" scripts/test_replay_pending.py
"$PYTHON_BIN" scripts/test_paper_artifact_hardening.py
"$PYTHON_BIN" scripts/test_search_paper_obstructions.py
"$PYTHON_BIN" scripts/test_orthus_threshold_rounding.py
"$PYTHON_BIN" scripts/generate_formalization_table.py --check
"$PYTHON_BIN" scripts/check_fast_assumption.py
"$PYTHON_BIN" scripts/check_trust.py
"$PYTHON_BIN" scripts/check_trust.py --allow-cataloged-fast-assumptions
"$PYTHON_BIN" scripts/check_fast_import_boundary.py
"$PYTHON_BIN" scripts/check_local_lean_imports.py
"$PYTHON_BIN" scripts/check_numeric_import_boundary.py
"$PYTHON_BIN" scripts/test_numeric_import_boundary.py
"$PYTHON_BIN" scripts/test_direct_geometric_samples.py
"$PYTHON_BIN" scripts/test_upper_short_tail.py
"$PYTHON_BIN" scripts/test_tyurin_outer_plan.py
"$PYTHON_BIN" scripts/test_dominant_shared_caps.py
"$PYTHON_BIN" scripts/test_threshold_dominant_constant_cover128.py
"$PYTHON_BIN" scripts/test_sparse_upper_hybrid.py
"$PYTHON_BIN" scripts/test_sparse_upper_contour_build.py
"$PYTHON_BIN" scripts/test_fast_validation_roots.py
"$PYTHON_BIN" scripts/check_certificate_workflow.py
"$PYTHON_BIN" scripts/test_check_paper_ci_impact.py
"$PYTHON_BIN" scripts/check_runner_hardening.py
"$PYTHON_BIN" scripts/test_runner_hardening.py
"$PYTHON_BIN" scripts/test_compute_replay_digest.py
"$PYTHON_BIN" scripts/test_native_shadow_replay.py
"$PYTHON_BIN" scripts/test_kernel_stage_receipt.py
"$PYTHON_BIN" scripts/test_validate_dispatch.py
"$PYTHON_BIN" scripts/test_run_builtin_lints_isolated.py
"$PYTHON_BIN" scripts/test_run_instrumented_kernel_validation.py
"$PYTHON_BIN" scripts/test_compute_fast_cache_key.py
"$PYTHON_BIN" scripts/test_sample_selection.py
"$PYTHON_BIN" scripts/test_compute_sample_cache_key.py
"$PYTHON_BIN" scripts/test_validation_roots.py
"$PYTHON_BIN" scripts/compute_fast_cache_key.py
# The exact ThresholdLower76 obstruction certificate is replayed by
# validate_certificates.sh and the proof-of-record lane, never by fast CI.
./scripts/build_validation_group.sh fast

echo "Fast validation passed."
