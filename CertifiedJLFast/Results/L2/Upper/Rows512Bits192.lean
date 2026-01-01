/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Assembly
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFinal
import CertifiedJL.Statements.L2.Upper
import CertifiedJLFast.Assumptions.Families.L2Upper.Rows512Bits192

/-! # Assumption-backed 512-row, 192-bit upper specialization -/

namespace CertifiedJLFast.Results.L2.Upper.Rows512Bits192

open CertifiedJL
open scoped BigOperators ENNReal

private theorem normalizedTernaryL2Upper607
    {d : ℕ} (a : Fin d → ℝ) (hnorm : ∑ i, a i ^ 2 = 1) :
    eventProbability (sparseRademacherMatrix 512 d)
        (fun J => (607 : ℝ) < realProjectionSqNorm a J) <
      failureTarget 192 := by
  exact CertificateAssembly.normalizedTernaryL2Upper607
    Assumptions.sparse_l2_upper_contour_512_bits192_assumed a hnorm

/-- Assumption-backed balanced-ternary upper tail at threshold `607`. -/
theorem ternaryL2Upper607 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192) := by
  intro q d w
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  by_cases hw : w = 0
  · have hzero :
        eventProbability (sparseRademacherMatrix 512 d)
            (L2UpperFailure (NonnegativeRatio.ofNat 607) q w) ≤
          eventProbability (sparseRademacherMatrix 512 d)
            (fun _ => False) := by
      apply eventProbability_mono
      intro J hJ
      simp [L2UpperFailure, hw, modularProjectionSqNorm, sqNorm, rowDot,
        centeredMod, ZMod.valMinAbs_zero] at hJ
    calc
      eventProbability (sparseRademacherMatrix 512 d)
          (L2UpperFailure (NonnegativeRatio.ofNat 607) q w) ≤
          eventProbability (sparseRademacherMatrix 512 d)
            (fun _ => False) := hzero
      _ = 0 := eventProbability_false _
      _ < failureTarget 192 := by
        unfold failureTarget
        rw [pos_iff_ne_zero]
        exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))
  · apply (eventProbability_mono (p := sparseRademacherMatrix 512 d)
      (fun J hfailure => ?_)).trans_lt
      (normalizedTernaryL2Upper607
        (sparseUpperNormalizedCoefficient w)
        (sum_sq_sparseUpperNormalizedCoefficient w hw))
    have hrowNat : 607 * sqNorm w < projectionSqNorm J w := by
      have hfailure' : 607 * sqNorm w < modularProjectionSqNorm q J w := by
        simpa [L2UpperFailure, NonnegativeRatio.ofNat] using hfailure
      exact hfailure'.trans_le (modularProjectionSqNorm_le_projectionSqNorm J w)
    have hV : 0 < (sqNorm w : ℝ) := by
      exact_mod_cast (sqNorm_pos_iff w).2 hw
    have hrow :
        (607 : ℝ) * (sqNorm w : ℝ) < (projectionSqNorm J w : ℝ) := by
      exact_mod_cast hrowNat
    rw [realProjectionSqNorm_eq_projectionSqNorm_div J w hw]
    exact (lt_div_iff₀ hV).2 hrow

end CertifiedJLFast.Results.L2.Upper.Rows512Bits192
