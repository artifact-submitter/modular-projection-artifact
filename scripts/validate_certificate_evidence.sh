#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"
source "$PROJECT_ROOT/scripts/validation_environment.sh"

echo "# Checking certificate catalog and payload identity"
python3 ./scripts/check_certificate_catalog.py
python3 ./scripts/test_check_certificate_catalog.py

echo "# Checking theorem contract"
python3 ./scripts/check_contract.py

echo "# Checking promoted counterexample evidence and generated coverage"
python3 ./scripts/check_counterexample_catalog.py
python3 ./scripts/render_counterexample_coverage.py --check
python3 ./scripts/check_counterexample_searches.py
python3 ./scripts/test_search_counterexamples.py

echo
echo "# Checking public result and API catalogs"
python3 ./scripts/check_public_catalogs.py

echo
echo "# Checking exhaustive replay-family coverage"
python3 ./scripts/check_replay_families.py
python3 ./scripts/test_check_replay_families.py

echo
echo "# Checking certificate workflow topology"
python3 ./scripts/check_certificate_workflow.py
python3 ./scripts/test_check_certificate_workflow.py
python3 ./scripts/test_sparse_upper_contour_build.py
python3 ./scripts/test_check_paper_ci_impact.py
python3 ./scripts/test_compute_replay_digest.py
python3 ./scripts/test_kernel_stage_receipt.py
python3 ./scripts/test_validate_dispatch.py
python3 ./scripts/test_run_builtin_lints_isolated.py
python3 ./scripts/test_sample_selection.py
python3 ./scripts/test_compute_sample_cache_key.py

echo
echo "# Checking trust boundary"
python3 ./scripts/check_fast_assumption.py
python3 ./scripts/check_trust.py --allow-cataloged-fast-assumptions

echo
echo "# Checking numerical import boundaries"
python3 ./scripts/check_numeric_import_boundary.py
python3 ./scripts/test_numeric_import_boundary.py
python3 ./scripts/test_threshold_dominant_constant_cover128.py

# Generate the adaptive cover once, then compare every base/floor source byte.
echo "# Checking deterministic lower-certificate generation"
python3 ./scripts/threshold_dominant_constant_cover128.py --shard-size 4 \
  --check-all-dir CertifiedJL/Certificates/Families/L2Lower/Shared/Dominant
python3 ./scripts/lower_certificate_shard_topology.py --check

# Search only proposes raw plans; production replay remains kernel checked.
lake build CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarsePartition128
lake env lean --run scripts/GenerateNearCoarsePlans.lean --check
