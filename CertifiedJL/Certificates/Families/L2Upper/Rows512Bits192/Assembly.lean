/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Spec
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Final

/-! # Shared assembly for the 512-row, 192-bit sparse upper tail -/

open scoped BigOperators ENNReal

namespace CertifiedJL.CertificateAssembly

/-- The exact contour contract implies the normalized threshold-607 tail. -/
theorem normalizedTernaryL2Upper607
    (verified : CertificateContracts.SparseL2UpperContour512Bits192)
    {d : ℕ} (a : Fin d → ℝ) (hnorm : ∑ i, a i ^ 2 = 1) :
    eventProbability (sparseRademacherMatrix 512 d)
        (fun J => (607 : ℝ) < realProjectionSqNorm a J) <
      failureTarget 192 := by
  simpa [SparseUpperContour.rows, SparseUpperContour.threshold,
    SparseUpperContour.securityBits] using
    SparseUpperContour.ShortTail.normalized607_of_contract verified a hnorm

end CertifiedJL.CertificateAssembly
