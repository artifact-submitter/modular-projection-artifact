/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified

/-! # Kernel-verified endpoint provider for 512 rows and 256 bits -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2UpperContourRows512Bits256Threshold681_verified :
    CertificateContracts.SparseL2UpperContourRows512Bits256Threshold681 := by
  exact ⟨
    Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified.allBoxesCheck_eq_true,
    Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified.highProfileCheck_eq_true⟩

end CertifiedJL.CertificateProviders
