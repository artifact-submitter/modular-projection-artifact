/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Diffuse.Soundness.Floor73Endpoints

/-! # Narrow verified diffuse endpoints at tilt `5/2` -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDiffuseFloor73Endpoints_verified :
    CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints :=
  SparseThresholdDiffuseFloor73.verified

end CertifiedJL.CertificateProviders
