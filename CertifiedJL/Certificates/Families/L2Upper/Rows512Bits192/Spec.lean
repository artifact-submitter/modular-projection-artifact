/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Soundness

/-! # Semantic certificate contract for the 512-row, 192-bit upper contour -/

namespace CertifiedJL.CertificateContracts

/-- Actual contour endpoint facts consumed by the unchanged strict threshold-607
assembly. The contract does not prescribe a quadrature mesh or proof strategy. -/
def SparseL2UpperContour512Bits192 : Prop :=
  (∀ box ∈ SparseUpperContour.profileBoxes,
    ∀ profile : ℝ, profile ∈ Set.Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      SparseUpperContour.boxActualPrefactorValue box *
        (∫ frequency : ℝ in Set.Ioi 0,
          SparseUpperContour.actualBoxQuadratureIntegrand box profile frequency) <
        (box.target : ℝ)) ∧
  SparseUpperContour.highProfileBound.upperRat < 1 / 2

end CertifiedJL.CertificateContracts
