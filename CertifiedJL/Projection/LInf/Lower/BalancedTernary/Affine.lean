/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.ThresholdLower
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedProfiles
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SingletonConditioning
import CertifiedJL.Probability.Finite.PMF
import CertifiedJL.Probability.Product.RowTensorization
import CertifiedJL.Projection.Counterexamples.Shared.SparseThreeAtomCenteredArc

/-!
# Direct affine infinity-norm lower tails

The input profile determines one of two cases. A coefficient larger than
twice the accepted radius gives a conditional three-atom bound of one half.
Otherwise a cap at most three eighths forces the diffuse coefficient condition,
and a retained wrapped-Gaussian estimate bounds the affine small-ball event.
The shift may differ in every row and is fixed before the matrix is sampled.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL

open Probability

/-- Exact one-row affine small-projection event. -/
def AffineLInfRowPass (cap : NonnegativeRatio) (q b : ℕ)
    {d : ℕ} (shift : ℤ) (w : Fin d → ℤ) (row : Fin d → ℤ) : Prop :=
  cap.denominator ^ 2 *
      (centeredMod q (shift + ∑ i, row i * w i)).natAbs ^ 2 ≤
    cap.numerator ^ 2 * b ^ 2

/-- The squared natural-number event is exactly the division-free arc event. -/
theorem affineLInfRowPass_iff_scaledArc
    (cap : NonnegativeRatio) (q b : ℕ)
    {d : ℕ} (shift : ℤ) (w : Fin d → ℤ) (row : Fin d → ℤ) :
    AffineLInfRowPass cap q b shift w row ↔
      ScaledCenteredArcPass q cap.denominator (cap.numerator * b)
        (shift + ∑ i, row i * w i) := by
  unfold AffineLInfRowPass ScaledCenteredArcPass
  rw [← mul_pow, ← mul_pow]
  exact pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide)

/-- A large centered coefficient bounds every shifted row event by one half.
No norm or modulus-margin hypothesis is needed for this case. -/
theorem sparseRow_affineLInf_large_toReal_le_half
    (cap : NonnegativeRatio) {q d b : ℕ} (shift : ℤ) (w : Fin d → ℤ)
    (hcentered : CenteredInput q w)
    (hlarge : ∃ i, 2 * (cap.numerator * b) <
      cap.denominator * (w i).natAbs) :
    (eventProbability (sparseRademacherRow d)
      (AffineLInfRowPass cap q b shift w)).toReal ≤ (1 / 2 : ℝ) := by
  classical
  obtain ⟨i, hi⟩ := hlarge
  apply sparseRademacherRow_eventProbability_toReal_le_of_complFirst
    (singletonCoordinateMask i) (AffineLInfRowPass cap q b shift w) (1 / 2 : ℝ)
  intro other
  let z := shift + sparseRowSeedComplDot (singletonCoordinateMask i) other w
  have hevent :
      eventProbability
        ((PMF.uniformOfFintype
          (SparseRowSeedPart (singletonCoordinateMask i))).map
          (fun selected => sparseRow
            (joinSparseRowSeed (singletonCoordinateMask i) selected other)))
        (AffineLInfRowPass cap q b shift w) =
      eventProbability
        ((PMF.uniformOfFintype
          (SparseRowSeedPart (singletonCoordinateMask i))).map
          (sparseRowSingletonSeedEquiv i))
        (fun bits => ScaledCenteredArcPass q cap.denominator (cap.numerator * b)
          (z + sparseBit bits * w i)) := by
    apply eventProbability_map_congr
    intro selected
    rw [affineLInfRowPass_iff_scaledArc, sparseRow_join_singleton_dot]
    simp only [z, add_assoc]
  rw [hevent, map_uniformSparseRowSingletonSeed]
  have hpull :
      eventProbability (PMF.uniformOfFintype (Bool × Bool))
        (fun bits => ScaledCenteredArcPass q cap.denominator (cap.numerator * b)
          (z + sparseBit bits * w i)) =
      eventProbability sparseEntryPMF
        (fun x => ScaledCenteredArcPass q cap.denominator (cap.numerator * b)
          (z + x * w i)) := by
    unfold sparseEntryPMF eventProbability
    rw [PMF.map_comp]
    rfl
  rw [hpull]
  apply sparseEntry_scaledCenteredArcPass_toReal_le_half_of_centered
    z (w i) ?_ hi
  have hci := hcentered i
  simp only [centeredInterval, Set.mem_Icc] at hci
  have habs : |w i| ≤ ((q / 2 : ℕ) : ℤ) := abs_le.mpr hci
  have hnat : (w i).natAbs ≤ q / 2 := by
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  exact (Nat.mul_le_mul_left 2 hnat).trans (Nat.mul_div_le q 2)

/-- A pointwise real majorant bounds a sparse-row event. This keeps the
finite seed experiment explicitly connected to the analytic row integral. -/
theorem sparseRow_eventProbability_toReal_le_integral
    {d : ℕ} (event : (Fin d → ℤ) → Prop) [DecidablePred event]
    (F : (Fin d → ℤ) → ℝ)
    (hpoint : ∀ row, (if event row then (1 : ℝ) else 0) ≤ F row) :
    (eventProbability (sparseRademacherRow d) event).toReal ≤
      ∫ row, F row ∂(sparseRademacherRow d).toMeasure := by
  classical
  let p : PMF (SparseRowSeed d) := PMF.uniformOfFintype (SparseRowSeed d)
  have hseed := finitePMF_eventProbability_toReal_le_integral p
    (fun seed => event (sparseRow seed)) (fun seed => F (sparseRow seed))
    (fun seed => hpoint (sparseRow seed))
  have hevent :
      eventProbability (sparseRademacherRow d) event =
        eventProbability p (fun seed => event (sparseRow seed)) := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    unfold eventProbability
    rw [PMF.map_comp]
    rfl
  have hintegral :
      (∫ seed, F (sparseRow seed) ∂p.toMeasure) =
        ∫ row, F row ∂(sparseRademacherRow d).toMeasure := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    rw [← PMF.toMeasure_map (p := p) (f := @sparseRow d)
      (measurable_of_finite sparseRow)]
    rw [integral_map_of_stronglyMeasurable (measurable_of_finite sparseRow)
      (measurable_of_countable F).stronglyMeasurable]
  rw [hevent, ← hintegral]
  exact hseed

/-- A retained wrapped estimate gives a closed affine small-ball estimate. -/
theorem sparseRow_affineLInf_toReal_le_of_wrapped
    (cap : NonnegativeRatio) {q d b : ℕ} (shift : ℤ) (w : Fin d → ℤ)
    (support : Finset (Fin d)) {t K : ℝ}
    (hq : Odd q) (hb : 0 < b) (ht : 0 < t)
    (hwrapped : ∫ row, wrappedGaussianKernel q (t / (b : ℝ) ^ 2)
        (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure ≤ K) :
    (eventProbability (sparseRademacherRow d)
      (AffineLInfRowPass cap q b shift w)).toReal ≤
      Real.exp (t * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K := by
  classical
  let C : ℝ := t * ((cap.numerator : ℝ) / cap.denominator) ^ 2
  let s : ℝ := t / (b : ℝ) ^ 2
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hden : 0 < (cap.denominator : ℝ) := by exact_mod_cast cap.denominator_pos
  have hs : 0 < s := by dsimp [s]; positivity
  have hpoint (row : Fin d → ℤ) :
      (if AffineLInfRowPass cap q b shift w row then (1 : ℝ) else 0) ≤
        Real.exp C * Real.exp (-s * affineSparseLowerRowKernel q shift w row) := by
    by_cases hp : AffineLInfRowPass cap q b shift w row
    · rw [if_pos hp, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hsquare :
          (cap.denominator : ℝ) ^ 2 *
            (centeredMod q (shift + ∑ i, row i * w i) : ℝ) ^ 2 ≤
          (cap.numerator : ℝ) ^ 2 * (b : ℝ) ^ 2 := by
        have hcast : (cap.denominator : ℝ) ^ 2 *
            ((centeredMod q (shift + ∑ i, row i * w i)).natAbs : ℝ) ^ 2 ≤
            (cap.numerator : ℝ) ^ 2 * (b : ℝ) ^ 2 := by
          exact_mod_cast hp
        have habs (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
          rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
        simpa only [habs, sq_abs] using hcast
      have hbound :
          (centeredMod q (shift + ∑ i, row i * w i) : ℝ) ^ 2 ≤
            ((cap.numerator : ℝ) / cap.denominator) ^ 2 * (b : ℝ) ^ 2 := by
        calc
          _ ≤ (cap.numerator : ℝ) ^ 2 * (b : ℝ) ^ 2 /
              (cap.denominator : ℝ) ^ 2 :=
            (le_div_iff₀ (sq_pos_of_pos hden)).2 (by nlinarith [hsquare])
          _ = _ := by ring
      have hmul := mul_le_mul_of_nonneg_left hbound hs.le
      dsimp [C, s] at *
      have heq : t / (b : ℝ) ^ 2 *
          (((cap.numerator : ℝ) / cap.denominator) ^ 2 * (b : ℝ) ^ 2) =
          t * ((cap.numerator : ℝ) / cap.denominator) ^ 2 := by
        field_simp
      rw [heq] at hmul
      linarith
    · rw [if_neg hp]
      positivity
  have hprob := sparseRow_eventProbability_toReal_le_integral
    (AffineLInfRowPass cap q b shift w)
    (fun row => Real.exp C * Real.exp (-s * affineSparseLowerRowKernel q shift w row))
    hpoint
  rw [integral_const_mul] at hprob
  have hrow := (sparseRow_affineCenteredGaussian_le_wrappedGaussianKernel_restrict
    shift w support hq hs).trans hwrapped
  exact hprob.trans (mul_le_mul_of_nonneg_left hrow (Real.exp_pos C).le)

/-- General shifted probability bound from a single diffuse wrapped provider. -/
theorem ternaryAffineLInfThresholdLower_probability_le_of_wrappedRowBound
    (rows : ℕ) (cap : NonnegativeRatio) (t K : ℝ)
    (hwrapped : SparseThresholdDiffuseWrappedRowBoundAt t K)
    (hcap : 8 * cap.numerator ≤ 3 * cap.denominator)
    (ht : 0 < t) (_hK : 0 ≤ K)
    (q d : ℕ) (w : Fin d → ℤ) (b : ℕ) (shift : Fin rows → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w) (hb : 0 < b)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineLInfThresholdSmallProjection
        { distribution := .balancedTernary, rows := rows, coordinateCap := cap,
          modulusMargin := NonnegativeRatio.ofNat 3 } b q shift w)).toReal ≤
      (max (1 / 2 : ℝ)
        (Real.exp (t * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K)) ^ rows := by
  change (eventProbability (sparseRademacherMatrix rows d)
    (fun J => ∀ j, AffineLInfRowPass cap q b (shift j) w (J j))).toReal ≤ _
  apply sparseRademacherMatrix_eventProbability_varyingRows_toReal_le_pow
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_left _ _)
  · intro j
    by_cases hlarge : ∃ i, 2 * (cap.numerator * b) <
        cap.denominator * (w i).natAbs
    · exact (sparseRow_affineLInf_large_toReal_le_half cap (shift j) w
        hcentered hlarge).trans (le_max_left _ _)
    · have hdiffuse : ∀ i, 4 * (w i).natAbs ≤ 3 * b := by
        intro i
        have hi : cap.denominator * (w i).natAbs ≤ 2 * (cap.numerator * b) :=
          le_of_not_gt (fun hi => hlarge ⟨i, hi⟩)
        have hh := Nat.mul_le_mul_right b hcap
        have hdi := cap.denominator_pos
        nlinarith
      obtain ⟨support, hsupport⟩ := hwrapped q d w b hq hb hnorm hmargin hdiffuse
      exact (sparseRow_affineLInf_toReal_le_of_wrapped cap (shift j) w
        support hq hb ht hsupport).trans (le_max_right _ _)

/-- Optimize between two diffuse wrapped providers before tensorizing. Both
providers apply to the same diffuse input; no union bound is involved. -/
theorem ternaryAffineLInfThresholdLower_probability_le
    (rows : ℕ) (cap : NonnegativeRatio) (t₁ K₁ t₂ K₂ : ℝ)
    (hwrapped₁ : SparseThresholdDiffuseWrappedRowBoundAt t₁ K₁)
    (hwrapped₂ : SparseThresholdDiffuseWrappedRowBoundAt t₂ K₂)
    (hcap : 8 * cap.numerator ≤ 3 * cap.denominator)
    (ht₁ : 0 < t₁) (hK₁ : 0 ≤ K₁) (ht₂ : 0 < t₂) (hK₂ : 0 ≤ K₂)
    (q d : ℕ) (w : Fin d → ℤ) (b : ℕ) (shift : Fin rows → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w) (hb : 0 < b)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineLInfThresholdSmallProjection
        { distribution := .balancedTernary, rows := rows, coordinateCap := cap,
          modulusMargin := NonnegativeRatio.ofNat 3 } b q shift w)).toReal ≤
      (max (1 / 2 : ℝ) (min
        (Real.exp (t₁ * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K₁)
        (Real.exp (t₂ * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K₂))) ^ rows := by
  by_cases hle :
      Real.exp (t₁ * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K₁ ≤
      Real.exp (t₂ * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K₂
  · rw [min_eq_left hle]
    exact ternaryAffineLInfThresholdLower_probability_le_of_wrappedRowBound
      rows cap t₁ K₁ hwrapped₁ hcap ht₁ hK₁ q d w b shift hq hcentered hb hnorm hmargin
  · rw [min_eq_right (le_of_not_ge hle)]
    exact ternaryAffineLInfThresholdLower_probability_le_of_wrappedRowBound
      rows cap t₂ K₂ hwrapped₂ hcap ht₂ hK₂ q d w b shift hq hcentered hb hnorm hmargin

/-- Direct shifted infinity-norm theorem from any diffuse wrapped-row
provider. Large and diffuse cases are properties of the fixed input, so no
union-bound loss is incurred. -/
theorem ternaryAffineLInfThresholdLowerTail_of_wrappedRowBound
    (rows bits : ℕ) (cap : NonnegativeRatio) (t K : ℝ)
    (hwrapped : SparseThresholdDiffuseWrappedRowBoundAt t K)
    (hcap : 8 * cap.numerator ≤ 3 * cap.denominator)
    (ht : 0 < t) (hK : 0 ≤ K)
    (hhalf : (1 / 2 : ℝ) ^ rows < (2 : ℝ)⁻¹ ^ bits)
    (hratio : (Real.exp (t * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K) ^ rows <
      (2 : ℝ)⁻¹ ^ bits) :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := rows, coordinateCap := cap,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget bits) := by
  intro q d w b shift hq hcentered hb hnorm hmargin
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  have hmarginNat : 3 * b ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmargin
  have hbound := ternaryAffineLInfThresholdLower_probability_le_of_wrappedRowBound
    rows cap t K hwrapped hcap ht hK q d w b shift hq hcentered hb hnorm hmarginNat
  have hmax :
      (max (1 / 2 : ℝ)
        (Real.exp (t * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K)) ^ rows <
      (2 : ℝ)⁻¹ ^ bits := by
    by_cases hle : (1 / 2 : ℝ) ≤
        Real.exp (t * ((cap.numerator : ℝ) / cap.denominator) ^ 2) * K
    · simpa only [max_eq_right hle] using hratio
    · simpa only [max_eq_left (le_of_not_ge hle)] using hhalf
  have hreal := hbound.trans_lt hmax
  rw [← ENNReal.toReal_lt_toReal
    (by unfold eventProbability; exact PMF.apply_ne_top _ _) (by simp [failureTarget])]
  simpa [failureTarget] using hreal

end CertifiedJL
