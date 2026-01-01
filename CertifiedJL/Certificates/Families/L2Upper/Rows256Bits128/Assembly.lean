/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Spec
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Final

/-! # Shared assembly for the sparse upper-tail result -/

namespace CertifiedJL.CertificateAssembly

theorem sparseL2Upper128
    (hybrid : CertificateContracts.SparseL2UpperHybrid) :
    SparseUpper128Statement :=
  SparseUpperHybrid.sparseUpper128_of_verified hybrid

end CertifiedJL.CertificateAssembly
