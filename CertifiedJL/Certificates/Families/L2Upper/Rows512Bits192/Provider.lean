/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Spec
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Replay.Verified
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.HighProfile

/-! # Kernel-verified provider for the 512-row, 192-bit upper contour -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2UpperContour512Bits192_verified :
    CertificateContracts.SparseL2UpperContour512Bits192 := by
  exact ⟨
    fun _ hbox _ hp => SparseUpperContour.ShortTail.all_endpoints hbox hp,
    SparseUpperContour.highProfile_upperRat_lt⟩

end CertifiedJL.CertificateProviders
