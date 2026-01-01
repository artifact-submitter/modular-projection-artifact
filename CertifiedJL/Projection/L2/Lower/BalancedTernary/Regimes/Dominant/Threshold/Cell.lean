/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.Cell
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Soundness
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Kernel

/-!
# Public-threshold dominant cells

This is the certificate-free soundness layer for the joint
`K ≥ squaredNormFloor` event. Unlike the retired cap-relative cell expression, its
exponential threshold is an independent upper bound for `b²/A²`.
-/

open scoped BigOperators
open MeasureTheory

namespace CertifiedJL

/-- Inactive nonzero modular images with an independent lower bound for
`q / A`. -/
noncomputable def thresholdDominantCellInactiveWrap
    (_lower upper modulusLower z : ℚ) : ℝ :=
  let B : ℝ := modulusLower
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))
  2 * Real.exp (-alpha * B ^ 2) /
    (1 - Real.exp (-3 * alpha * B ^ 2))

/-- Active nonzero modular images with an independent lower bound for
`q / A`. -/
noncomputable def thresholdDominantCellActiveWrap
    (_lower upper modulusLower z : ℚ) : ℝ :=
  let B : ℝ := modulusLower
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))
  Real.exp (-alpha * (B - 1) ^ 2) /
      (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
    Real.exp (-alpha * (B + 1) ^ 2) /
      (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))

noncomputable def thresholdDominantCellInactiveRow
    (lower upper modulusLower z : ℚ) : ℝ :=
  let sLower : ℝ := (z : ℝ) * (lower : ℝ)
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  let theta := Real.exp (-Real.pi ^ 2 / (1 + sUpper))
  (1 / Real.sqrt (1 + sLower)) *
      (1 + 2 * theta / (1 - theta ^ 3)) +
    thresholdDominantCellInactiveWrap lower upper modulusLower z

noncomputable def thresholdDominantCellActiveRow
    (lower upper modulusLower z : ℚ) : ℝ :=
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  Real.exp (-(z : ℝ) / (1 + sUpper)) *
      dominantCellRho lower upper z +
    thresholdDominantCellActiveWrap lower upper modulusLower z

/-- Joint conditional majorant. Counts below `squaredNormFloor` contribute exactly
zero. -/
noncomputable def thresholdDominantCellConditionalMajorantAt
    (rows squaredNormFloor : ℕ) (cell : ThresholdDominantCellRowBoundsAt rows)
    (k : Fin (rows + 1)) : ℝ :=
  if (k : ℕ) < squaredNormFloor then 0
  else if cell.z k = 0 then 1
  else
    min 1
      (Real.exp
          (squaredNormFloor * (cell.z k : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCellActiveRow cell.lower cell.upper
            cell.modulusLower (cell.z k) ^ (k : ℕ) *
        thresholdDominantCellInactiveRow cell.lower cell.upper
            cell.modulusLower (cell.z k) ^
          (rows - (k : ℕ)))

/-- Compatibility specialization of the conditional majorant at 256 rows and
squared-norm floor 29. Its body intentionally preserves the original public
reduction behavior used by numeric certificate soundness proofs. -/
noncomputable def thresholdDominantCellConditionalMajorant
    (cell : ThresholdDominantCellRowBounds) (k : Fin 257) : ℝ :=
  if (k : ℕ) < 29 then 0
  else if cell.z k = 0 then 1
  else
    min 1
      (Real.exp
          (29 * (cell.z k : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCellActiveRow cell.lower cell.upper
            cell.modulusLower (cell.z k) ^ (k : ℕ) *
        thresholdDominantCellInactiveRow cell.lower cell.upper
            cell.modulusLower (cell.z k) ^
          (256 - (k : ℕ)))

@[simp]
theorem thresholdDominantCellConditionalMajorant_eq_at
    (cell : ThresholdDominantCellRowBounds) (k : Fin 257) :
    thresholdDominantCellConditionalMajorant cell k =
      thresholdDominantCellConditionalMajorantAt 256 29 cell k := by
  rfl

noncomputable def thresholdDominantCellMajorantAt
    (rows squaredNormFloor : ℕ)
    (cell : ThresholdDominantCellRowBoundsAt rows) : ℝ :=
  dominantBinomialAverageAt rows
    (thresholdDominantCellConditionalMajorantAt rows squaredNormFloor cell)

/-- Compatibility specialization of the complete cell majorant at 256 rows
and squared-norm floor 29. -/
noncomputable def thresholdDominantCellMajorant
    (cell : ThresholdDominantCellRowBounds) : ℝ :=
  dominantBinomialAverage (thresholdDominantCellConditionalMajorant cell)

@[simp]
theorem thresholdDominantCellMajorant_eq_at
    (cell : ThresholdDominantCellRowBounds) :
    thresholdDominantCellMajorant cell =
      thresholdDominantCellMajorantAt 256 29 cell := by
  unfold thresholdDominantCellMajorant thresholdDominantCellMajorantAt
  unfold dominantBinomialAverage
  apply Finset.sum_congr rfl
  intro k _
  rw [thresholdDominantCellConditionalMajorant_eq_at]

@[simp]
theorem matrixDominantActivity_sparseMatrixOfDominantView
    {m d : ℕ} (i : Fin d) (activity : DominantActivity m)
    (conditional : DominantConditionalSeeds (m := m) i) :
    matrixDominantActivity i
        (sparseMatrixOfDominantView i (activity, conditional)) = activity := by
  rw [sparseMatrixOfDominantView, matrixDominantActivity_sparseMatrix]
  simp

private theorem eventProbability_toReal_mono_thresholdCell
    {Omega : Type*} [Countable Omega] [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega] (p : PMF Omega)
    {event event' : Omega → Prop} (h : ∀ x, event x → event' x) :
    (eventProbability p event).toReal ≤
      (eventProbability p event').toReal := by
  rw [eventProbability_eq_toMeasure, eventProbability_eq_toMeasure]
  exact measureReal_mono h

private theorem dominantConditional_highActivity_event_eq_zero_at
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (rows squaredNormFloor : ℕ) (activity : DominantActivity rows)
    (hk : (dominantActivityCount activity : ℕ) < squaredNormFloor) :
    eventProbability (dominantConditionalMatrixPMF i activity)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) = 0 := by
  let p := PMF.uniformOfFintype (DominantConditionalSeeds (m := rows) i)
  let reconstruct : DominantConditionalSeeds (m := rows) i →
      Matrix (Fin rows) (Fin d) ℤ := fun conditional =>
    sparseMatrixOfDominantView i (activity, conditional)
  let event := fun J : Matrix (Fin rows) (Fin d) ℤ =>
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
        inputThreshold q w J ∧
      squaredNormFloor ≤ (dominantActivityCount (matrixDominantActivity i J) : ℕ)
  have himpossible (conditional : DominantConditionalSeeds (m := rows) i) :
      ¬ event (reconstruct conditional) := by
    intro hevent
    have hcount : matrixDominantActivity i (reconstruct conditional) =
        activity := by
      exact matrixDominantActivity_sparseMatrixOfDominantView
        i activity conditional
    change L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
        inputThreshold q w (reconstruct conditional) ∧
      squaredNormFloor ≤ (dominantActivityCount
        (matrixDominantActivity i (reconstruct conditional)) : ℕ) at hevent
    rw [hcount] at hevent
    omega
  have heq := eventProbability_map_congr p reconstruct
    (fun _ => ()) event (fun _ : Unit => False)
    (fun conditional => iff_false_intro (himpossible conditional))
  rw [dominantConditionalMatrixPMF]
  change eventProbability (p.map reconstruct) event = 0
  calc
    _ = eventProbability (p.map fun _ => ()) (fun _ : Unit => False) := heq
    _ = 0 := eventProbability_false _

/-- One fixed activity set satisfies the public-threshold cell majorant at an
arbitrary row count and squared-norm floor. -/
theorem dominantConditional_thresholdHighActivity_le_cellMajorant_of_rowKernels_at
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (hi : w i ≠ 0)
    (rows squaredNormFloor inputThreshold : ℕ)
    (activity : DominantActivity rows)
    (cell : ThresholdDominantCellRowBoundsAt rows)
    (hvalid : ThresholdDominantCellRowBoundsAt.Valid cell)
    (hr : dominantThresholdRatio w i inputThreshold ≤
      (cell.thresholdUpper : ℝ))
    (hrow : ∀ row,
      ∫ x, Real.exp
          (-(cell.z (dominantActivityCount activity) : ℝ) *
            dominantNormalizedRowKernel q w i x)
          ∂(dominantConditionalRowPMF i (activity row)).toMeasure ≤
        if activity row then
          thresholdDominantCellActiveRow cell.lower cell.upper
            cell.modulusLower
            (cell.z (dominantActivityCount activity))
        else
          thresholdDominantCellInactiveRow cell.lower cell.upper
            cell.modulusLower
            (cell.z (dominantActivityCount activity))) :
    (eventProbability (dominantConditionalMatrixPMF i activity)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
      thresholdDominantCellConditionalMajorantAt rows squaredNormFloor cell
        (dominantActivityCount activity) := by
  let k := dominantActivityCount activity
  by_cases hk : (k : ℕ) < squaredNormFloor
  · rw [thresholdDominantCellConditionalMajorantAt, if_pos hk]
    rw [dominantConditional_highActivity_event_eq_zero_at
      w i inputThreshold rows squaredNormFloor activity hk]
    simp
  · rw [thresholdDominantCellConditionalMajorantAt, if_neg hk]
    by_cases hz : cell.z k = 0
    · rw [if_pos hz]
      exact eventProbability_toReal_le_one _ _
    rw [if_neg hz]
    apply le_min
    · exact eventProbability_toReal_le_one _ _
    have hzposRat : 0 < cell.z k :=
      lt_of_le_of_ne (hvalid.2.2.2.2 k) (Ne.symm hz)
    have hzpos : 0 < (cell.z k : ℝ) := by exact_mod_cast hzposRat
    have hfailure :=
      dominantConditional_thresholdFailure_le_activeInactiveKernels_at
      w i hi rows squaredNormFloor inputThreshold activity (cell.z k : ℝ)
      (thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower (cell.z k))
      (thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower (cell.z k)) hzpos hrow
    have hsubset :
        (eventProbability (dominantConditionalMatrixPMF i activity)
          (fun J =>
            L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
                inputThreshold q w J ∧
              squaredNormFloor ≤ (dominantActivityCount
                (matrixDominantActivity i J) : ℕ))).toReal ≤
        (eventProbability (dominantConditionalMatrixPMF i activity)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
            inputThreshold q w)).toReal := by
      apply eventProbability_toReal_mono_thresholdCell
      exact fun _ h => h.1
    have hproduct :
        0 ≤ thresholdDominantCellActiveRow cell.lower cell.upper
              cell.modulusLower (cell.z k) ^ (k : ℕ) *
          thresholdDominantCellInactiveRow cell.lower cell.upper
              cell.modulusLower (cell.z k) ^
            (rows - (k : ℕ)) := by
      rw [← prod_dominantActivity_ite activity]
      apply Finset.prod_nonneg
      intro row _
      exact (integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)).trans
          (hrow row)
    have hexp :
        Real.exp (squaredNormFloor * (cell.z k : ℝ) *
            dominantThresholdRatio w i inputThreshold) ≤
          Real.exp (squaredNormFloor * (cell.z k : ℝ) *
            (cell.thresholdUpper : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hr
        (mul_nonneg (by positivity) hzpos.le)
    calc
      _ ≤ (eventProbability (dominantConditionalMatrixPMF i activity)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
            inputThreshold q w)).toReal := hsubset
      _ ≤ Real.exp (squaredNormFloor * (cell.z k : ℝ) *
            dominantThresholdRatio w i inputThreshold) *
          (thresholdDominantCellActiveRow cell.lower cell.upper
              cell.modulusLower (cell.z k) ^ (k : ℕ) *
            thresholdDominantCellInactiveRow cell.lower cell.upper
              cell.modulusLower (cell.z k) ^
              (rows - (k : ℕ))) := by
        simpa [k, mul_assoc] using hfailure
      _ ≤ Real.exp (squaredNormFloor * (cell.z k : ℝ) *
            (cell.thresholdUpper : ℝ)) *
          (thresholdDominantCellActiveRow cell.lower cell.upper
              cell.modulusLower (cell.z k) ^ (k : ℕ) *
            thresholdDominantCellInactiveRow cell.lower cell.upper
              cell.modulusLower (cell.z k) ^
              (rows - (k : ℕ))) :=
        mul_le_mul_of_nonneg_right hexp hproduct
      _ = _ := by
        dsimp [k]
        ring

/-- Compatibility specialization of fixed-activity threshold cells at 256
rows and squared-norm floor 29. -/
theorem dominantConditional_thresholdHighActivity_le_cellMajorant_of_rowKernels
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (hi : w i ≠ 0)
    (inputThreshold : ℕ) (activity : DominantActivity 256)
    (cell : ThresholdDominantCellRowBounds) (hvalid : cell.Valid)
    (hr : dominantThresholdRatio w i inputThreshold ≤
      (cell.thresholdUpper : ℝ))
    (hrow : ∀ row,
      ∫ x, Real.exp
          (-(cell.z (dominantActivityCount activity) : ℝ) *
            dominantNormalizedRowKernel q w i x)
          ∂(dominantConditionalRowPMF i (activity row)).toMeasure ≤
        if activity row then
          thresholdDominantCellActiveRow cell.lower cell.upper
            cell.modulusLower
            (cell.z (dominantActivityCount activity))
        else
          thresholdDominantCellInactiveRow cell.lower cell.upper
            cell.modulusLower
            (cell.z (dominantActivityCount activity))) :
    (eventProbability (dominantConditionalMatrixPMF i activity)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
      thresholdDominantCellConditionalMajorant cell
        (dominantActivityCount activity) := by
  simpa [thresholdDominantCellConditionalMajorant,
      thresholdDominantCellConditionalMajorantAt] using
    dominantConditional_thresholdHighActivity_le_cellMajorant_of_rowKernels_at
      w i hi 256 29 inputThreshold activity cell hvalid hr hrow

/-- Exact binomial averaging of fixed-activity public-threshold cells at an
arbitrary row count and squared-norm floor. -/
theorem dominantThresholdHighActivity_le_cellMajorant_of_conditional_at
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (rows squaredNormFloor : ℕ) (cell : ThresholdDominantCellRowBoundsAt rows)
    (hconditional : ∀ activity : DominantActivity rows,
      (eventProbability (dominantConditionalMatrixPMF i activity)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
        thresholdDominantCellConditionalMajorantAt rows squaredNormFloor cell
          (dominantActivityCount activity)) :
    (eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
      thresholdDominantCellMajorantAt rows squaredNormFloor cell := by
  exact dominantEventProbability_le_binomialAverage_of_conditional_at
    rows i _ (thresholdDominantCellConditionalMajorantAt
      rows squaredNormFloor cell) hconditional

/-- Compatibility specialization of exact threshold-cell averaging at 256
rows and squared-norm floor 29. -/
theorem dominantThresholdHighActivity_le_cellMajorant_of_conditional
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (cell : ThresholdDominantCellRowBounds)
    (hconditional : ∀ activity : DominantActivity 256,
      (eventProbability (dominantConditionalMatrixPMF i activity)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
        thresholdDominantCellConditionalMajorant cell
          (dominantActivityCount activity)) :
    (eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
      thresholdDominantCellMajorant cell := by
  rw [thresholdDominantCellMajorant_eq_at]
  exact
    dominantThresholdHighActivity_le_cellMajorant_of_conditional_at
      w i inputThreshold 256 29 cell fun activity => by
        simpa using hconditional activity

end CertifiedJL
