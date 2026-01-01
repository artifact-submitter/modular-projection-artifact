/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Assembly
import CertifiedJL.Projection.LInf.Upper.Matrix
import CertifiedJLFast.Assumptions.Families.OneRow975

/-! # Assumption-backed 256-row result specializations -/

namespace CertifiedJLFast.Results.LInf.Upper.Rows256Bits128

/-- Balanced-ternary strict modular infinity upper tail at coordinate
threshold `(39/4) * ‖w‖₂`. The internal 141-bit one-row certificate loses
exactly eight bits across 256 rows. -/
theorem ternaryLInfUpper39Over4Bits133 :
    CertifiedJL.LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateThreshold :=
          { numerator := 39, denominator := 4, denominator_pos := by decide } }
      (CertifiedJL.failureTarget 133) := by
  apply CertifiedJL.LInfUpperTailAt.of_oneRow
    (rowBudget := CertifiedJL.failureTarget 141)
  · decide
  · intro d w
    change CertifiedJL.eventProbability (CertifiedJL.sparseRademacherRow d)
      (fun row => |CertifiedJL.euclideanRowDot row w| >
        (39 / 4 : ℝ) * ‖w‖) < CertifiedJL.failureTarget 141
    rw [CertifiedJL.eventProbability_congr
      (CertifiedJL.sparseRademacherRow d)
      (event' := CertifiedJL.SparseOneRow975Event w) (by intro row; rfl)]
    simpa [CertifiedJL.sparseOneRowSecurityBits, CertifiedJL.failureTarget] using
      CertifiedJL.CertificateAssembly.sparseOneRow975
        Assumptions.moderate_grid_assumed
        Assumptions.sparse_one_row_envelope_assumed d w
  · simpa using CertifiedJL.nsmul_failureTarget_add_le
      (shares := 256) (bits := 133) (slackBits := 8) (by decide)

/-- The 128-bit interface specialization of the primary 133-bit matrix
theorem. -/
theorem ternaryLInfUpper39Over4 :
    CertifiedJL.LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateThreshold :=
          { numerator := 39, denominator := 4, denominator_pos := by decide } }
      (CertifiedJL.failureTarget 128) := by
  apply ternaryLInfUpper39Over4Bits133.mono_budget
  unfold CertifiedJL.failureTarget
  exact pow_le_pow_of_le_one (by positivity) (by norm_num) (by norm_num)

end CertifiedJLFast.Results.LInf.Upper.Rows256Bits128
