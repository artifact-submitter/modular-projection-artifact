/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedSupport
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Analytic128

/-!
# Analytic retained-profile cap for the dominant 128-bit branch

This module connects the lightweight interval replay to the coupled Holder
moment.  It deliberately concerns only the central nonmodular moment; modular
image tails are composed once at the row level by the dominant provider.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL

/-- Every coupled Holder factor in the retained profile is at most `12/25`.
The total normalized mass is `x`, the dominant coordinate has mass one, and
`y` is one residual coordinate's normalized Holder weight. -/
theorem retainedDominantGaussianCosineMoment_le_twelve_twentyfive_of_geometry
    (geometry : CertificateContracts.SparseL2ThresholdDominantRetainedGeometry)
    {x y : ℝ} (hxLower : 3 / 2 ≤ x) (hxUpper : x ≤ 11 / 5)
    (hy : 0 < y) (hyUpper : y ≤ 1) :
    retainedGaussianCosineMoment ((23 / 10) * x) (1 / x) y ≤
      ENNReal.ofReal (12 / 25) := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) hxLower
  have hax : (1 : ℝ) < x :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3 / 2) hxLower
  by_cases hyCoarse : y ≤ 4 / 5
  · have hmoment := retainedGaussianCosineMoment_le_semanticCoarseCentral
      hx (by norm_num : (0 : ℝ) < 1) hax hy hyCoarse
    rw [show (1 : ℝ) / x = 1 / x by rfl] at hmoment
    exact hmoment.trans (ENNReal.ofReal_mono
      (geometry.coarseCentral hxLower hxUpper).le)
  · have hyChord : 1 / 2 ≤ y := by linarith
    have hmoment := retainedGaussianCosineMoment_le_semanticChordCentral
      hx (by norm_num : (0 : ℝ) < 1) hax hyChord hyUpper
    rw [show (1 : ℝ) / x = 1 / x by rfl] at hmoment
    exact hmoment.trans (ENNReal.ofReal_mono
      (geometry.chordCentral
        hxLower hxUpper (le_of_not_ge hyCoarse) hyUpper).le)

/-- Compatibility wrapper for the original 128-bit replay contract. -/
theorem retainedDominantGaussianCosineMoment_le_twelve_twentyfive_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128)
    {x y : ℝ} (hxLower : 3 / 2 ≤ x) (hxUpper : x ≤ 11 / 5)
    (hy : 0 < y) (hyUpper : y ≤ 1) :
    retainedGaussianCosineMoment ((23 / 10) * x) (1 / x) y ≤
      ENNReal.ofReal (12 / 25) :=
  retainedDominantGaussianCosineMoment_le_twelve_twentyfive_of_geometry
    replay.retainedGeometry hxLower hxUpper hy hyUpper

/-- The retained compact vector has central (zero modular image) row moment
at most `12/25`.  The hypotheses are the exact integral mass bounds emitted
by `exists_halfCutoff_dominantRemainder_subprofile`. -/
theorem sparseRow_retainedDominantCentral_le_twelve_twentyfive_of_geometry
    (geometry : CertificateContracts.SparseL2ThresholdDominantRetainedGeometry)
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (support : Finset (Fin (Fintype.card (DominantRemainderIndex i))))
    (hi : w i ≠ 0)
    (hlower : dominantAmplitude w i ^ 2 ≤
      2 * sqNorm (fun j => if j ∈ support then
        dominantRemainderFinWeights w i j else 0))
    (hupper : 5 * sqNorm (fun j => if j ∈ support then
        dominantRemainderFinWeights w i j else 0) <
      6 * dominantAmplitude w i ^ 2) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-((23 / 10 : ℝ) / (dominantAmplitude w i : ℝ) ^ 2) *
            (((∑ j, row j *
              (if j ∈ dominantLiftSupport i support then w j else 0) : ℤ) : ℝ) ^ 2))
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal (12 / 25) := by
  let A := dominantAmplitude w i
  let compact : Fin d → ℤ := fun j =>
    if j ∈ dominantLiftSupport i support then w j else 0
  let V := sqNorm (fun j => if j ∈ support then
    dominantRemainderFinWeights w i j else 0)
  let W : ℝ := (A : ℝ) ^ 2 + V
  let x : ℝ := W / (A : ℝ) ^ 2
  let a : Fin d → ℝ := fun j => (compact j : ℝ) / Real.sqrt W
  let r : ℝ := 1 / x
  let S : Finset (Fin d) := Finset.univ.filter fun j => j ≠ i ∧ a j ≠ 0
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hV : 0 < V := by
    dsimp [V]
    omega
  have hVreal : (0 : ℝ) < V := by exact_mod_cast hV
  have hW : 0 < W := by dsimp [W]; positivity
  have hsqrtW : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have hsqrtWne : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 hW).ne'
  have hxLower : 3 / 2 ≤ x := by
    dsimp [x, W]
    have hlowerR : (A : ℝ) ^ 2 ≤ 2 * (V : ℝ) := by exact_mod_cast hlower
    apply (le_div_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  have hxUpper : x ≤ 11 / 5 := by
    dsimp [x, W]
    have hupperR : 5 * (V : ℝ) < 6 * (A : ℝ) ^ 2 := by exact_mod_cast hupper
    apply (div_le_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  have hx : 0 < x :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) hxLower
  have hcompactI : compact i = w i := by
    simp [compact]
  have hcompactResidual : dominantRemainderFinWeights compact i =
      fun j => if j ∈ support then dominantRemainderFinWeights w i j else 0 :=
    dominantRemainderFinWeights_restrict_liftSupport w i support
  have hcompactSq : ∑ j, (compact j : ℝ) ^ 2 = W := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
    have hreindex :
        (∑ j : DominantRemainderIndex i, (compact j.1 : ℝ) ^ 2) =
          ∑ k, (dominantRemainderFinWeights compact i k : ℝ) ^ 2 := by
      exact ((dominantRemainderEquivFin i).symm.sum_comp
        (fun j : DominantRemainderIndex i => (compact j.1 : ℝ) ^ 2)).symm
    rw [hreindex, hcompactResidual]
    have hres :
        (∑ k, ((fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) k : ℝ) ^ 2) =
          (V : ℝ) := by
      simpa only [V] using (realCast_sqNorm
        (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0)).symm
    rw [hres, hcompactI]
    have hiSq : (w i : ℝ) ^ 2 = (A : ℝ) ^ 2 := by
      dsimp [A, dominantAmplitude]
      have h := congrArg (fun z : ℤ => (z : ℝ))
        (Int.natAbs_sq (w i)).symm
      norm_num at h
      simpa using h
    rw [hiSq]
  have ha : ∑ j, a j ^ 2 = 1 := by
    dsimp [a]
    calc
      ∑ j, ((compact j : ℝ) / Real.sqrt W) ^ 2 =
          (∑ j, (compact j : ℝ) ^ 2) / W := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_pow, hsqrtW]
      _ = 1 := by rw [hcompactSq]; exact div_self hW.ne'
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hx).2
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3 / 2) hxLower)
  have hir : a i ^ 2 = r := by
    dsimp [a, r, x]
    rw [hcompactI, div_pow, hsqrtW]
    have hiSq : (w i : ℝ) ^ 2 = (A : ℝ) ^ 2 := by
      have h := congrArg (fun z : ℤ => (z : ℝ))
        (Int.natAbs_sq (w i)).symm
      norm_num at h
      simpa [A, dominantAmplitude] using h
    rw [hiSq]
    field_simp [hW.ne', (sq_pos_of_pos hAreal).ne']
  have hiA : a i ≠ 0 := by
    dsimp [a]
    rw [hcompactI]
    exact div_ne_zero (by exact_mod_cast hi) hsqrtWne
  have hS : ∀ j, j ∈ S ↔ j ≠ i ∧ a j ≠ 0 := by
    intro j
    simp [S]
  have hremNorm : dominantRemainderSqNorm compact i = V := by
    rw [← sqNorm_dominantRemainderFinWeights, hcompactResidual]
  have hmoment : ∀ j, j ∈ S →
      retainedGaussianCosineMoment ((23 / 10) * x) r
          (a j ^ 2 / (1 - r)) ≤ ENNReal.ofReal (12 / 25) := by
    intro j hj
    have hji : j ≠ i := (hS j).1 hj |>.1
    have haj : a j ≠ 0 := (hS j).1 hj |>.2
    have hcNonzero : compact j ≠ 0 := by
      dsimp [a] at haj
      exact fun h => haj (by simp [h])
    have hcSq : (compact j).natAbs ^ 2 ≤ V := by
      rw [← hremNorm]
      unfold dominantRemainderSqNorm
      exact Finset.single_le_sum
        (f := fun k : DominantRemainderIndex i =>
          (compact k.1).natAbs ^ 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨j, hji⟩)
    let y : ℝ := (compact j : ℝ) ^ 2 / V
    have hy : 0 < y := by
      dsimp [y]
      have hcReal : (compact j : ℝ) ≠ 0 := by exact_mod_cast hcNonzero
      positivity
    have hyUpper : y ≤ 1 := by
      dsimp [y]
      have hcSqReal : (compact j : ℝ) ^ 2 ≤ (V : ℝ) := by
        have hcast : ((compact j).natAbs ^ 2 : ℝ) ≤ (V : ℝ) := by
          exact_mod_cast hcSq
        have hsq : (compact j : ℝ) ^ 2 = ((compact j).natAbs ^ 2 : ℝ) := by
          have h := congrArg (fun z : ℤ => (z : ℝ))
            (Int.natAbs_sq (compact j)).symm
          norm_num at h
          simpa using h
        rw [hsq]
        exact hcast
      exact (div_le_one hVreal).2 hcSqReal
    have hyEq : a j ^ 2 / (1 - r) = y := by
      dsimp [a, r, x, y, W]
      rw [div_pow, hsqrtW]
      field_simp [hW.ne', (sq_pos_of_pos hAreal).ne', hVreal.ne']
      ring
    rw [hyEq, show r = 1 / x by rfl]
    exact retainedDominantGaussianCosineMoment_le_twelve_twentyfive_of_geometry
      geometry hxLower hxUpper hy hyUpper
  have hcentral := sparseRow_retained_nonmodulated_le_of_moment_cap
    a i ((23 / 10) * x) r (12 / 25) S
    (by positivity) hr0 hr1 ha hir hiA hS (by norm_num) hmoment
  convert hcentral using 1
  apply congrArg ENNReal.ofReal
  apply integral_congr_ae
  filter_upwards [] with row
  congr 1
  have hdot : realRowDot row a =
      ((∑ j, row j * compact j : ℤ) : ℝ) / Real.sqrt W := by
    dsimp [realRowDot, a]
    calc
      ∑ j, (row j : ℝ) * ((compact j : ℝ) / Real.sqrt W) =
          ∑ j, ((row j : ℝ) * (compact j : ℝ)) / Real.sqrt W := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ j, (row j : ℝ) * (compact j : ℝ)) / Real.sqrt W := by
        rw [Finset.sum_div]
      _ = ((∑ j, row j * compact j : ℤ) : ℝ) / Real.sqrt W := by
        push_cast
        rfl
  rw [hdot]
  change
    -((23 / 10 : ℝ) / (A : ℝ) ^ 2) *
        (((∑ j, row j * compact j : ℤ) : ℝ) ^ 2) =
      -((23 / 10 : ℝ) * x) *
        (((((∑ j, row j * compact j : ℤ) : ℝ) / Real.sqrt W)) ^ 2)
  dsimp [x]
  field_simp [hW.ne', (sq_pos_of_pos hAreal).ne', hsqrtWne]
  rw [hsqrtW]

/-- Compatibility wrapper for the original 128-bit replay contract. -/
theorem sparseRow_retainedDominantCentral_le_twelve_twentyfive_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128)
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (support : Finset (Fin (Fintype.card (DominantRemainderIndex i))))
    (hi : w i ≠ 0)
    (hlower : dominantAmplitude w i ^ 2 ≤
      2 * sqNorm (fun j => if j ∈ support then
        dominantRemainderFinWeights w i j else 0))
    (hupper : 5 * sqNorm (fun j => if j ∈ support then
        dominantRemainderFinWeights w i j else 0) <
      6 * dominantAmplitude w i ^ 2) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-((23 / 10 : ℝ) / (dominantAmplitude w i : ℝ) ^ 2) *
            (((∑ j, row j *
              (if j ∈ dominantLiftSupport i support then w j else 0) : ℤ) : ℝ) ^ 2))
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal (12 / 25) :=
  sparseRow_retainedDominantCentral_le_twelve_twentyfive_of_geometry
    replay.retainedGeometry w i support hi hlower hupper

end CertifiedJL
