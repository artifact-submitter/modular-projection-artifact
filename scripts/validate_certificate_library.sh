#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"
source "$repo_root/scripts/validation_environment.sh"

./scripts/validate_certificate_sparse_lower.sh

export CERTIFIEDJL_ASSEMBLY_ONLY=1
export CERTIFIEDJL_LIBRARY_ONLY=1
exec ./scripts/validate_certificates.sh
