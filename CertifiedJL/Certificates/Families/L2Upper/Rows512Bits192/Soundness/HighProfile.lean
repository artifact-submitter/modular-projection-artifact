/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Core

/-! # Independent high-profile endpoint replay

This check is deliberately separate from the forty low-profile contour
shards so a precision regression fails before the expensive replay begins.
-/

namespace CertifiedJL
namespace SparseUpperContour

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1024 in
theorem highProfileCheck_eq_true : highProfileCheck = true := by
  decide +kernel

theorem highProfile_upperRat_lt : highProfileBound.upperRat < 1 / 2 :=
  Interval.upperLTCheck_sound highProfileCheck_eq_true

end SparseUpperContour
end CertifiedJL
