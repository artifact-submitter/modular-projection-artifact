/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Assembly
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Provider

/-! # Kernel-verified sparse upper-tail theorem assembly -/

namespace CertifiedJL

/-- Internal assembly of the sharp sparse upper-tail statement contract. -/
theorem sparseUpper128_assembly : SparseUpper128Statement :=
  CertificateAssembly.sparseL2Upper128
    CertificateProviders.sparseL2UpperHybrid_verified

end CertifiedJL
