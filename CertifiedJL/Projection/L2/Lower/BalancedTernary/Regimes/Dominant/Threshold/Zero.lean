/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Soundness.ThresholdBits128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Cell

/-!
# Exact zero-residual dominant threshold branch

When the residual ratio is zero, every coefficient except the selected one
vanishes.  On the balanced-ternary support the modular projection squared norm is therefore
exactly the active-row count times the selected amplitude squared.  The
joint event with at least 29 active rows is empty.
-/

open scoped BigOperators

namespace CertifiedJL

private theorem dominantRemainderSqNorm_eq_zero_of_ratio_eq_zero
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (hi : w i ≠ 0)
    (hu : dominantResidualRatio w i = 0) :
    dominantRemainderSqNorm w i = 0 := by
  have hA : (dominantAmplitude w i : ℝ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < dominantAmplitude w i := by
      exact_mod_cast dominantAmplitude_pos hi
    positivity
  have hUreal : (dominantRemainderSqNorm w i : ℝ) = 0 := by
    exact (div_eq_zero_iff.mp (by simpa [dominantResidualRatio] using hu)).resolve_right hA
  exact_mod_cast hUreal

private theorem dominantRemainder_coordinate_eq_zero
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hU : dominantRemainderSqNorm w i = 0)
    (j : DominantRemainderIndex i) :
    w j.1 = 0 := by
  have hall : ∀ k : DominantRemainderIndex i, (w k.1).natAbs ^ 2 = 0 := by
    rw [dominantRemainderSqNorm,
      Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le ((w k.1).natAbs ^ 2))]
      at hU
    exact fun k => hU k (Finset.mem_univ k)
  have habs : (w j.1).natAbs = 0 := by
    exact (Nat.pow_eq_zero.mp (hall j)).1
  exact Int.natAbs_eq_zero.mp habs

private theorem dominantRemainderSeedDot_eq_zero_of_sqNorm_eq_zero
    {m d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hU : dominantRemainderSqNorm w i = 0)
    (seed : DominantRemainderSeeds (m := m) i) (row : Fin m) :
    dominantRemainderSeedDot seed w row = 0 := by
  unfold dominantRemainderSeedDot
  apply Finset.sum_eq_zero
  intro j _
  rw [dominantRemainder_coordinate_eq_zero w i hU j, mul_zero]

private theorem centeredInterval_neg {q : ℕ} {z : ℤ}
    (hz : z ∈ centeredInterval q) :
    -z ∈ centeredInterval q := by
  rcases hz with ⟨hzlow, hzhigh⟩
  constructor <;> omega

private theorem centeredMod_signBit_mul_eq
    {q : ℕ} (hq : Odd q) {z : ℤ} (hz : z ∈ centeredInterval q)
    (sign : Bool) :
    centeredMod q (signBit sign * z) = signBit sign * z := by
  apply centeredMod_eq_self hq
  cases sign
  · simpa [signBit] using centeredInterval_neg hz
  · simpa [signBit] using hz

private theorem modularProjectionSqNorm_sparseMatrixOfDominantView_eq_activity
    {q m d : ℕ} (w : Fin d → ℤ) (i : Fin d) (hq : Odd q)
    (hcentered : CenteredInput q w)
    (hU : dominantRemainderSqNorm w i = 0)
    (view : DominantSeedView (m := m) i) :
    modularProjectionSqNorm q (sparseMatrixOfDominantView i view) w =
      (dominantActivityCount view.1 : ℕ) * (w i).natAbs ^ 2 := by
  unfold modularProjectionSqNorm
  have hzero : centeredMod q 0 = 0 := by
    apply centeredMod_eq_self hq
    constructor
    · exact neg_nonpos.mpr (Int.natCast_nonneg _)
    · exact Int.natCast_nonneg _
  have hrow (row : Fin m) :
      (centeredMod q
          (rowDot (sparseMatrixOfDominantView i view) w row)).natAbs ^ 2 =
        if view.1 row then (w i).natAbs ^ 2 else 0 := by
    rw [sparseMatrixOfDominantView_rowDot]
    rw [dominantRemainderSeedDot_eq_zero_of_sqNorm_eq_zero
      w i hU view.2.2 row]
    cases hactivity : view.1 row
    · simp [hzero]
    · simp only [↓reduceIte, add_zero]
      rw [centeredMod_signBit_mul_eq hq (hcentered i)]
      cases view.2.1 row <;> simp [signBit]
  simp_rw [hrow]
  change (∑ row, if view.1 row = true then (w i).natAbs ^ 2 else 0) = _
  rw [Finset.sum_ite]
  simp [dominantActivityCount, Probability.boolSupport]

/-- At zero residual ratio, the public-threshold failure event jointly with
`K ≥ squaredNormFloor` has exactly zero probability. -/
theorem sparseThresholdDominantHighActivity_zeroResidual_probability_eq_zero_at
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (rows squaredNormFloor : ℕ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hi : w i ≠ 0) (hu : dominantResidualRatio w i = 0) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) = 0 := by
  let p := PMF.uniformOfFintype (DominantSeedView (m := rows) i)
  let reconstruct : DominantSeedView (m := rows) i →
      Matrix (Fin rows) (Fin d) ℤ := sparseMatrixOfDominantView i
  let event := fun J : Matrix (Fin rows) (Fin d) ℤ =>
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
        inputThreshold q w J ∧
      squaredNormFloor ≤ (dominantActivityCount (matrixDominantActivity i J) : ℕ)
  have hU := dominantRemainderSqNorm_eq_zero_of_ratio_eq_zero w i hi hu
  have hnorm' : inputThreshold ^ 2 ≤ (w i).natAbs ^ 2 := by
    have hsq : sqNorm w = (w i).natAbs ^ 2 := by
      rw [sqNorm_eq_dominant_add_remainder w i, hU, add_zero]
    simpa [InputThresholdAtMostNorm, hsq] using hnorm
  have himpossible (view : DominantSeedView (m := rows) i) :
      ¬event (reconstruct view) := by
    intro hevent
    have hcount : matrixDominantActivity i (reconstruct view) = view.1 := by
      exact matrixDominantActivity_sparseMatrixOfDominantView i view.1 view.2
    have hk : squaredNormFloor ≤ (dominantActivityCount view.1 : ℕ) := by
      simpa only [event, reconstruct, hcount] using hevent.2
    have henergy := modularProjectionSqNorm_sparseMatrixOfDominantView_eq_activity
      w i hq hcentered hU view
    have hfailure :
        modularProjectionSqNorm q (reconstruct view) w <
          squaredNormFloor * inputThreshold ^ 2 := by
      simpa [event, reconstruct, L2ThresholdLowerFailure,
        NonnegativeRatio.ofNat] using hevent.1
    rw [henergy] at hfailure
    have : squaredNormFloor * inputThreshold ^ 2 ≤
        (dominantActivityCount view.1 : ℕ) * (w i).natAbs ^ 2 := by
      exact Nat.mul_le_mul hk hnorm'
    omega
  have heq := eventProbability_map_congr p reconstruct
    (fun _ => ()) event (fun _ : Unit => False)
    (fun view => iff_false_intro (himpossible view))
  rw [sparseRademacherMatrix_eq_map_uniformDominantView i]
  change eventProbability (p.map reconstruct) event = 0
  calc
    _ = eventProbability (p.map fun _ => ()) (fun _ : Unit => False) := heq
    _ = 0 := eventProbability_false _

/-- Compatibility specialization of the zero-residual theorem at 256 rows and
squared-norm floor 29. -/
theorem sparseThresholdDominantHighActivity_zeroResidual_probability_eq_zero
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hi : w i ≠ 0) (hu : dominantResidualRatio w i = 0) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) = 0 :=
  sparseThresholdDominantHighActivity_zeroResidual_probability_eq_zero_at
    w inputThreshold i 256 29 hq hcentered hnorm hi hu

end CertifiedJL
