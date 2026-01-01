#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"
source "$repo_root/scripts/validation_environment.sh"

export CERTIFIEDJL_CANARIES_ONLY=1
exec ./scripts/validate_certificates.sh
