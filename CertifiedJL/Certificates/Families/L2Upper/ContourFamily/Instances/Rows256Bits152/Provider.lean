/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Verified

/-! # Kernel-verified endpoint provider for 256 rows and 152 bits -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2UpperContourRows256Bits152Threshold365_verified :
    CertificateContracts.SparseL2UpperContourRows256Bits152Threshold365 := by
  exact ⟨
    Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Verified.allBoxesCheck_eq_true,
    Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Verified.highProfileCheck_eq_true⟩

end CertifiedJL.CertificateProviders
