/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Spec

/-! # Fast assumption for the 512-row, 192-bit upper contour -/

namespace CertifiedJLFast.Assumptions

axiom sparse_l2_upper_contour_512_bits192_assumed :
  CertifiedJL.CertificateContracts.SparseL2UpperContour512Bits192

end CertifiedJLFast.Assumptions
