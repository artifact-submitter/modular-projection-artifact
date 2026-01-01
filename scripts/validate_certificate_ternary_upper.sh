#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"
source "$PROJECT_ROOT/scripts/validation_environment.sh"

echo "# Checking deterministic balanced-ternary upper-certificate generation"
lake build CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Core \
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Generator \
  CertifiedJL.Tests.SparseUpperContourFamilyFixture \
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287 \
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406 \
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509 \
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681
python3 ./scripts/run_ternary_upper_generation_checks.py

echo
echo "# Replaying balanced-ternary upper proofs and upper-tail canaries"
lake build CertifiedJL.Tests.UpperTailCanaries
lake build CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified
./scripts/build_sparse_upper_contour_proofs.sh
./scripts/build_sparse_upper_contour_family_proofs.sh
