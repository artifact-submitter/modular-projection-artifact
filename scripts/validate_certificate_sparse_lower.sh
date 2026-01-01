#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"
source "$repo_root/scripts/validation_environment.sh"

python3 scripts/check_dependency_cache.py

echo "# Replaying cataloged balanced-ternary lower certificates"
exec ./scripts/build_validation_group.sh sparse-lower
