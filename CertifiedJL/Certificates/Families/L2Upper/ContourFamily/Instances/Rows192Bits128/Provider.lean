/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified

/-! # Kernel-verified endpoint provider for 192 rows and 128 bits -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2UpperContourRows192Bits128Threshold287_verified :
    CertificateContracts.SparseL2UpperContourRows192Bits128Threshold287 := by
  exact ⟨
    Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.allBoxesCheck_eq_true,
    Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.highProfileCheck_eq_true⟩

end CertifiedJL.CertificateProviders
