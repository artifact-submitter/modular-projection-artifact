#!/usr/bin/env bash

set -euo pipefail

PROJECT_ROOT="$(git rev-parse --show-toplevel)"
cd "$PROJECT_ROOT"
source "$PROJECT_ROOT/scripts/validation_environment.sh"

echo "# Replaying the Tyurin moderate certificate"
./scripts/build_moderate_certificate_proofs.sh
