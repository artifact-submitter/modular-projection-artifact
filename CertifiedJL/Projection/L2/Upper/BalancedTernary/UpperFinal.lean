/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContour
import CertifiedJL.Model.Vectors.SquaredNorm
import CertifiedJL.Probability.Product.RowTensorization
import CertifiedJL.Statements.L2.Upper.Rows256Bits128
import Mathlib.Tactic

/-!
# Final sparse upper-tail normalization

This module owns the exact conversion from the natural modular-projection-squared-norm event
to the normalized real projection-squared-norm event used by the contour theorem.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL

/-- Canonical real coefficient vector obtained from a nonzero integer vector. -/
noncomputable def sparseUpperNormalizedCoefficient {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) : ℝ :=
  (w i : ℝ) / Real.sqrt (sqNorm w : ℝ)

/-- The canonical upper-tail coefficient vector has squared norm one. -/
theorem sum_sq_sparseUpperNormalizedCoefficient
    {d : ℕ} (w : Fin d → ℤ) (hw : w ≠ 0) :
    ∑ i, sparseUpperNormalizedCoefficient w i ^ 2 = 1 := by
  have hV : 0 < (sqNorm w : ℝ) := by
    exact_mod_cast (sqNorm_pos_iff w).2 hw
  have hsqrt_sq : Real.sqrt (sqNorm w : ℝ) ^ 2 = (sqNorm w : ℝ) :=
    Real.sq_sqrt hV.le
  calc
    ∑ i, sparseUpperNormalizedCoefficient w i ^ 2 =
        ∑ i, (w i : ℝ) ^ 2 / (sqNorm w : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [sparseUpperNormalizedCoefficient, div_pow, hsqrt_sq]
    _ = (∑ i, (w i : ℝ) ^ 2) / (sqNorm w : ℝ) := by
      rw [Finset.sum_div]
    _ = (sqNorm w : ℝ) / (sqNorm w : ℝ) := by
      rw [realCast_sqNorm]
    _ = 1 := div_self hV.ne'

/-- The sparse fourth-moment profile is nonnegative. -/
theorem sparseProfileFourthMoment_nonneg
    {d : ℕ} (a : Fin d → ℝ) :
    0 ≤ sparseProfileFourthMoment a := by
  unfold sparseProfileFourthMoment
  positivity

/-- A coefficient vector of squared norm one has profile at most one. -/
theorem sparseProfileFourthMoment_le_one
    {d : ℕ} (a : Fin d → ℝ) (hnorm : ∑ i, a i ^ 2 = 1) :
    sparseProfileFourthMoment a ≤ 1 := by
  unfold sparseProfileFourthMoment
  calc
    ∑ i, a i ^ 4 ≤ ∑ i, a i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hcoord : a i ^ 2 ≤ 1 := by
        calc
          a i ^ 2 ≤ ∑ j, a j ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg (a j))
              (Finset.mem_univ i)
          _ = 1 := hnorm
      nlinarith [sq_nonneg (a i), sq_nonneg (a i ^ 2)]
    _ = 1 := hnorm

/-- Normalized real projection squared norm is unreduced natural projection squared norm divided by `sqNorm`. -/
theorem realProjectionSqNorm_eq_projectionSqNorm_div
    {m d : ℕ} (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ)
    (hw : w ≠ 0) :
    realProjectionSqNorm (sparseUpperNormalizedCoefficient w) J =
      (projectionSqNorm J w : ℝ) / (sqNorm w : ℝ) := by
  have hV : 0 < (sqNorm w : ℝ) := by
    exact_mod_cast (sqNorm_pos_iff w).2 hw
  have hsqrt_ne : Real.sqrt (sqNorm w : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hV).ne'
  have hsqrt_sq : Real.sqrt (sqNorm w : ℝ) ^ 2 = (sqNorm w : ℝ) :=
    Real.sq_sqrt hV.le
  have hdot (j : Fin m) :
      realRowDot (J j) (sparseUpperNormalizedCoefficient w) =
        (rowDot J w j : ℝ) / Real.sqrt (sqNorm w : ℝ) := by
    calc
      realRowDot (J j) (sparseUpperNormalizedCoefficient w) =
          (∑ i, (J j i : ℝ) * (w i : ℝ)) /
            Real.sqrt (sqNorm w : ℝ) := by
        rw [realRowDot, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [sparseUpperNormalizedCoefficient]
        ring
      _ = (rowDot J w j : ℝ) / Real.sqrt (sqNorm w : ℝ) := by
        rw [intRowDot_cast_eq_realRowDot]
        rfl
  unfold realProjectionSqNorm
  simp_rw [hdot]
  calc
    ∑ j, ((rowDot J w j : ℝ) / Real.sqrt (sqNorm w : ℝ)) ^ 2 =
        ∑ j, (rowDot J w j : ℝ) ^ 2 / (sqNorm w : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [div_pow, hsqrt_sq]
    _ = (∑ j, (rowDot J w j : ℝ) ^ 2) / (sqNorm w : ℝ) := by
      rw [Finset.sum_div]
    _ = (projectionSqNorm J w : ℝ) / (sqNorm w : ℝ) := by
      rw [← realCast_projectionSqNorm]

/-- Every strict modular upper failure lies in the normalized real upper event. -/
theorem sparseUpperFailure_imp_realProjectionSqNorm
    {q m d : ℕ} (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ)
    (hw : w ≠ 0)
    (hfailure : SparseUpperFailure q w J) :
    (sparseUpperThreshold : ℝ) <
      realProjectionSqNorm (sparseUpperNormalizedCoefficient w) J := by
  have hVnat : 0 < sqNorm w := (sqNorm_pos_iff w).2 hw
  have hV : 0 < (sqNorm w : ℝ) := by exact_mod_cast hVnat
  have hrowNat : sparseUpperThreshold * sqNorm w < projectionSqNorm J w :=
    hfailure.trans_le (modularProjectionSqNorm_le_projectionSqNorm J w)
  have hrow :
      (sparseUpperThreshold : ℝ) * (sqNorm w : ℝ) <
        (projectionSqNorm J w : ℝ) := by
    exact_mod_cast hrowNat
  rw [realProjectionSqNorm_eq_projectionSqNorm_div J w hw]
  exact (lt_div_iff₀' hV).2 (by simpa [mul_comm] using hrow)

/-- Event-probability monotonicity at the modular-to-normalized boundary. -/
theorem sparseUpperFailure_probability_le_normalized
    {q m d : ℕ} (w : Fin d → ℤ) (hw : w ≠ 0) :
    eventProbability (sparseRademacherMatrix m d) (SparseUpperFailure q w) ≤
      eventProbability (sparseRademacherMatrix m d)
        (fun J => (sparseUpperThreshold : ℝ) <
          realProjectionSqNorm (sparseUpperNormalizedCoefficient w) J) := by
  apply eventProbability_mono
  intro J hJ
  exact sparseUpperFailure_imp_realProjectionSqNorm J w hw hJ

/-- Convert the real-valued probability endpoint used by the analytic and
certificate layers back to the public `ENNReal` failure target. -/
theorem eventProbability_lt_failureTarget_of_toReal_lt
    {α : Type*} [MeasurableSpace α] (p : PMF α) (event : α → Prop)
    (bits : ℕ)
    (hreal : (eventProbability p event).toReal < (2 : ℝ)⁻¹ ^ bits) :
    eventProbability p event < failureTarget bits := by
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by simp [failureTarget])]
  simpa [failureTarget] using hreal

/--
The normalized real-squared-norm theorem is the only analytic input needed for the
public natural sparse upper-tail statement.
-/
theorem sparseUpper128_of_realProjectionSqNorm
    (hnormalized : ∀ (d : ℕ) (a : Fin d → ℝ),
      ∑ i, a i ^ 2 = 1 →
      eventProbability (sparseRademacherMatrix rowCount d)
          (fun J => (sparseUpperThreshold : ℝ) <
            realProjectionSqNorm a J) <
        failureTarget securityBits) :
    SparseUpper128Statement := by
  intro q d w
  by_cases hw : w = 0
  · have hzero :
        eventProbability (sparseRademacherMatrix rowCount d)
            (SparseUpperFailure q w) ≤
          eventProbability (sparseRademacherMatrix rowCount d)
            (fun _ => False) := by
      apply eventProbability_mono
      intro J hJ
      simp [SparseUpperFailure, hw, modularProjectionSqNorm, sqNorm, rowDot,
        centeredMod, ZMod.valMinAbs_zero] at hJ
    calc
      eventProbability (sparseRademacherMatrix rowCount d)
          (SparseUpperFailure q w) ≤
          eventProbability (sparseRademacherMatrix rowCount d)
            (fun _ => False) := hzero
      _ = 0 := eventProbability_false _
      _ < failureTarget securityBits := by
        unfold failureTarget
        rw [pos_iff_ne_zero]
        exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))
  · exact (sparseUpperFailure_probability_le_normalized w hw).trans_lt
      (hnormalized d (sparseUpperNormalizedCoefficient w)
        (sum_sq_sparseUpperNormalizedCoefficient w hw))

/-- The low-profile contour and high-profile real bound cover all normalized vectors. -/
theorem sparseUpper128_of_profileSplit
    (hlow : ∀ (d : ℕ) (a : Fin d → ℝ),
      ∑ i, a i ^ 2 = 1 →
      sparseProfileFourthMoment a ≤ 1 / 20 →
      eventProbability (sparseRademacherMatrix rowCount d)
          (fun J => (sparseUpperThreshold : ℝ) <
            realProjectionSqNorm a J) <
        failureTarget securityBits)
    (hhigh : ∀ (d : ℕ) (a : Fin d → ℝ),
      ∑ i, a i ^ 2 = 1 →
      1 / 20 ≤ sparseProfileFourthMoment a →
      eventProbability (sparseRademacherMatrix rowCount d)
          (fun J => (sparseUpperThreshold : ℝ) <
            realProjectionSqNorm a J) <
        failureTarget securityBits) :
    SparseUpper128Statement := by
  apply sparseUpper128_of_realProjectionSqNorm
  intro d a hnorm
  rcases le_total (sparseProfileFourthMoment a) (1 / 20) with hprofile | hprofile
  · exact hlow d a hnorm hprofile
  · exact hhigh d a hnorm hprofile

end CertifiedJL
