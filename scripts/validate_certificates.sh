#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"
source "$PROJECT_ROOT/scripts/validation_environment.sh"

python3 ./scripts/check_dependency_cache.py

if [[ ${CERTIFIEDJL_LIBRARY_ONLY:-0} == 1 && \
      ${CERTIFIEDJL_CANARIES_ONLY:-0} == 1 ]]; then
  echo "library-only and canaries-only modes are mutually exclusive" >&2
  exit 2
fi

if [[ ${CERTIFIEDJL_CANARIES_ONLY:-0} != 1 ]]; then
  if [[ ${CERTIFIEDJL_ASSEMBLY_ONLY:-0} != 1 ]]; then
    ./scripts/validate_certificate_evidence.sh
    ./scripts/validate_certificate_moderate.sh
    ./scripts/validate_certificate_ternary_upper.sh
    ./scripts/validate_certificate_sparse_lower.sh
  fi

  echo
  echo "# Building the complete Lean library"
  lake build
fi

if [[ ${CERTIFIEDJL_LIBRARY_ONLY:-0} == 1 ]]; then
  exit 0
fi

echo
echo "# Building certificate tests and mutation canaries"
./scripts/build_validation_group.sh kernel-canaries

echo
echo "# Checking registered validation-root lint"
# Builtin linting follows imports, so roots that intentionally import generated
# certificates report inherited formatting warnings and cannot be useful lint
# gates.  Those roots are built above and their imports are covered by generator
# round-trip, trust, and proof replay.  Lint the clean structural roots here.
./scripts/run_builtin_lints_isolated.sh \
  CertifiedJL.Tests.StatementCanaries \
  CertifiedJL.Tests.ModelCanaries \
  CertifiedJL.Tests.MainTheoremNotation \
  CertifiedJL.Tests.ClosedIntervalTransfer \
  CertifiedJL.Tests.RowTensorization

./scripts/run_builtin_lints_isolated.sh CertifiedJL.Tests.FiniteConditioningLower

./scripts/run_builtin_lints_isolated.sh \
  CertifiedJL.Tests.SeedPartition \
  CertifiedJL.Tests.OneRowCertificateCanaries \
  CertifiedJL.Tests.OneRowReplayCanaries

./scripts/run_builtin_lints_isolated.sh CertifiedJL.Tests.EndpointRiemann

echo
echo "CertifiedJL certificate validation passed."
