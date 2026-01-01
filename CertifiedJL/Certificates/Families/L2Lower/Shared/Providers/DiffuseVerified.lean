/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Diffuse.Soundness.HighEndpoints128
import CertifiedJL.Certificates.Families.L2Lower.Shared.Diffuse.Soundness.LowModularTail128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.LowScalar

/-! # Narrow verified diffuse providers shared by centered and affine tails

Importing these three semantic providers does not replay the unrelated
near or dominant covers from the complete threshold-L2 provider.
-/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDiffuseLowScalar128_verified :
    CertificateContracts.SparseL2ThresholdDiffuseLowScalar128 where
  lowBand := ThresholdDiffuseLowScalar.sparseScalarF_lowBand_lt
  highBand := ThresholdDiffuseLowScalar.sparseScalarF_highBand_lt

theorem sparseL2ThresholdDiffuseLowModularTail128_verified :
    CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128 :=
  SparseThresholdDiffuse.verified

theorem sparseL2ThresholdDiffuseHighEndpoints128_verified :
    CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128 :=
  SparseThresholdDiffuseHighNumeric128.verified

end CertifiedJL.CertificateProviders
