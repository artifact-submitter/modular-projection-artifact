#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

# The production sparse certificate is one finite `Nat` fold over the 308
# retained cells of the denominator-1,200 mesh. No historical signed-interval
# shard path remains.
lake build CertifiedJL.Certificates.Families.OneRow975.Finite.NatIntervalAll

# Close the production certificate and its reader-facing theorem in this
# family stage rather than leaving their import tail to library assembly.
lake build \
  CertifiedJL.Certificates.Families.OneRow975.Finite \
  CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform
