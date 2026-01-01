/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Spec

/-! # Assumption-backed provider for sparse upper-tail replay -/

namespace CertifiedJLFast.Assumptions

axiom sparse_l2_upper_hybrid_assumed :
  CertifiedJL.CertificateContracts.SparseL2UpperHybrid

end CertifiedJLFast.Assumptions
