/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Scalar
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Kernel
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Fourier
import Mathlib.Algebra.Order.Floor.Div

/-!
# Shifted positive-Fourier deletion for a dominant coordinate

After conditioning on whether a distinguished coordinate is active, the
remaining row is an ordinary balanced-ternary row plus a fixed shift.  A
positive cosine majorant therefore has one extra phase factor.  Negative
phase factors can be discarded in an upper bound; nonnegative phase factors
retain the coordinate-deletion monotonicity of `ThresholdFourier`.

This is the dimension-free reduction needed for public-threshold dominant
inputs whose residual squared norm is not a priori bounded.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

private theorem thresholdIntegral_comp_eq_of_pmf_map_eq
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (p : PMF α) (q : PMF β) (X : α → γ) (Y : β → γ) (f : γ → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hf : Measurable f)
    (hmap : p.map X = q.map Y) :
    ∫ x, f (X x) ∂p.toMeasure = ∫ y, f (Y y) ∂q.toMeasure := by
  calc
    ∫ x, f (X x) ∂p.toMeasure =
        ∫ z, f z ∂Measure.map X p.toMeasure := by
      exact (integral_map hX.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(p.map X).toMeasure := by
      rw [PMF.toMeasure_map X p hX]
    _ = ∫ z, f z ∂(q.map Y).toMeasure := by rw [hmap]
    _ = ∫ z, f z ∂Measure.map Y q.toMeasure := by
      rw [PMF.toMeasure_map Y q hY]
    _ = ∫ y, f (Y y) ∂q.toMeasure := by
      exact integral_map hY.aemeasurable hf.aestronglyMeasurable

private theorem thresholdIntegral_even_comp_eq_of_square_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p : PMF α) (q : PMF β) (X : α → ℤ) (Y : β → ℤ) (f : ℤ → ℝ)
    (heven : Function.Even f)
    (hmap : p.map (fun x => X x ^ 2) = q.map (fun y => Y y ^ 2)) :
    ∫ x, f (X x) ∂p.toMeasure = ∫ y, f (Y y) ∂q.toMeasure := by
  classical
  let g : ℤ → ℝ := fun t =>
    if h : ∃ x : ℤ, x ^ 2 = t then f h.choose else 0
  have hfactor (x : ℤ) : g (x ^ 2) = f x := by
    dsimp [g]
    let hexists : ∃ y : ℤ, y ^ 2 = x ^ 2 := ⟨x, rfl⟩
    rw [dif_pos hexists]
    let y := Classical.choose hexists
    change f y = f x
    have hsquare : y ^ 2 = x ^ 2 := Classical.choose_spec hexists
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
    · rw [h]
    · rw [h]
      exact heven x
  calc
    ∫ x, f (X x) ∂p.toMeasure =
        ∫ x, g (X x ^ 2) ∂p.toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hfactor]
    _ = ∫ y, g (Y y ^ 2) ∂q.toMeasure :=
      thresholdIntegral_comp_eq_of_pmf_map_eq p q
        (fun x => X x ^ 2) (fun y => Y y ^ 2) g
        (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _) hmap
    _ = ∫ y, f (Y y) ∂q.toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hfactor]

private theorem thresholdCenteredMod_neg {q : ℕ} (hq : Odd q) (x : ℤ) :
    centeredMod q (-x) = -centeredMod q x := by
  apply (centeredMod_eq_iff hq (-x) (-centeredMod q x)).2
  constructor
  · simp
  · have hx := centeredMod_mem_centeredInterval hq x
    simp only [centeredInterval, Set.mem_Icc] at hx ⊢
    omega

private theorem thresholdExists_maximalSqCoordinate
    {d : ℕ} (w : Fin d → ℤ) (hw : w ≠ 0) :
    ∃ i, w i ≠ 0 ∧ ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2 := by
  have hnonzero : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    exact h i
  obtain ⟨i₀, hi₀⟩ := hnonzero
  let : Nonempty (Fin d) := ⟨i₀⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => (w j).natAbs ^ 2) Finset.univ_nonempty
  refine ⟨i, ?_, fun j => hi j (Finset.mem_univ j)⟩
  intro hwi
  have hi₀_sq : (w i₀).natAbs ^ 2 ≤ 0 := by
    simpa [hwi] using hi i₀ (Finset.mem_univ i₀)
  have hi₀_abs : (w i₀).natAbs = 0 := by nlinarith
  exact hi₀ (Int.natAbs_eq_zero.mp hi₀_abs)

/-- If any coordinate crosses the public dominant cutoff, a globally maximal
coordinate crosses it as well.  This is the exact selection rule required by
the compact residual reduction below. -/
theorem exists_maximalSqCoordinate_above_threshold
    {d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ)
    (hlarge : ∃ j, 49 * inputThreshold < 50 * (w j).natAbs) :
    ∃ i, w i ≠ 0 ∧
      (∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) ∧
      49 * inputThreshold < 50 * (w i).natAbs := by
  have hw : w ≠ 0 := by
    intro hw
    obtain ⟨j, hj⟩ := hlarge
    have hwj : w j = 0 := by simp [hw]
    simp [hwj] at hj
  obtain ⟨i, hi, hmax⟩ := thresholdExists_maximalSqCoordinate w hw
  obtain ⟨j, hj⟩ := hlarge
  have habs : (w j).natAbs ≤ (w i).natAbs :=
    (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp (hmax j)
  exact ⟨i, hi, hmax, lt_of_lt_of_le hj
    (Nat.mul_le_mul_left 50 habs)⟩

/-- A maximal dominant coordinate bounds every canonically reindexed residual
coefficient by the same squared amplitude. -/
theorem dominantRemainderFinWeights_sq_le_amplitude_sq_of_maximal
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) :
    ∀ j, (dominantRemainderFinWeights w i j).natAbs ^ 2 ≤
      dominantAmplitude w i ^ 2 := by
  intro j
  simpa [dominantRemainderFinWeights, dominantAmplitude] using
    hmax ((dominantRemainderEquivFin i).symm j).1

/-- If the residual already carries the public threshold mass, a maximal
dominant coordinate admits a residual subprofile whose squared mass is in
`[b², b² + A²)`.  Thus the unbounded residual regime reduces to a compact
profile rather than requiring infinitely many residual-ratio cells. -/
theorem exists_compact_dominantRemainder_subprofile
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (hpositive : 0 < inputThreshold)
    (hresidual : inputThreshold ^ 2 ≤ dominantRemainderSqNorm w i)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) :
    ∃ support : Finset
        (Fin (Fintype.card (DominantRemainderIndex i))),
      inputThreshold ^ 2 ≤
        sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) ∧
      sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) <
        inputThreshold ^ 2 + dominantAmplitude w i ^ 2 := by
  let n := Fintype.card (DominantRemainderIndex i)
  let v : Fin n → ℤ := dominantRemainderFinWeights w i
  let target := inputThreshold ^ 2
  let cap := dominantAmplitude w i ^ 2
  have htarget : 0 < target := by
    dsimp [target]
    exact pow_pos hpositive _
  have hcap : ∀ j, (v j).natAbs ^ 2 ≤ cap := by
    intro j
    exact dominantRemainderFinWeights_sq_le_amplitude_sq_of_maximal
      w i hmax j
  have htotal : target ≤ ∑ j, (v j).natAbs ^ 2 := by
    change target ≤ sqNorm v
    dsimp [target, v, n]
    rw [sqNorm_dominantRemainderFinWeights]
    exact hresidual
  obtain ⟨support, hlower, hupper⟩ :=
    exists_subset_sum_ge_lt_add_cap n target cap
      (fun j => (v j).natAbs ^ 2) htarget hcap htotal
  have hsquare :
      sqNorm (fun j => if j ∈ support then v j else 0) =
        ∑ j ∈ support, (v j).natAbs ^ 2 := by
    unfold sqNorm
    calc
      ∑ j, (if j ∈ support then v j else 0).natAbs ^ 2 =
          ∑ j, if j ∈ support then (v j).natAbs ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ support <;> simp [hj]
      _ = ∑ j ∈ support, (v j).natAbs ^ 2 := by
        rw [← Finset.sum_filter]
        simp
  refine ⟨support, ?_, ?_⟩
  · simpa [v, n, target, hsquare] using hlower
  · simpa [v, n, target, cap, hsquare] using hupper

/-- Integral ceiling of the `651/1000` squared-amplitude cutoff. -/
def dominantFourierCutoffMass (amplitude : ℕ) : ℕ :=
  (651 * amplitude ^ 2) ⌈/⌉ 1000

/-- In the high-residual regime, a maximal dominant coordinate admits a
subprofile with at least `651/1000` of its squared amplitude and overshoot
less than one squared amplitude.  The integral ceiling prevents a scale gap
for small amplitudes. -/
theorem exists_fourierCutoff_dominantRemainder_subprofile
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hi : w i ≠ 0)
    (hhigh : (dominantThresholdFourierCutoff : ℝ) ≤
      dominantResidualRatio w i)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) :
    ∃ support : Finset
        (Fin (Fintype.card (DominantRemainderIndex i))),
      651 * dominantAmplitude w i ^ 2 ≤
        1000 * sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) ∧
      sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) <
        dominantFourierCutoffMass (dominantAmplitude w i) +
          dominantAmplitude w i ^ 2 := by
  let A := dominantAmplitude w i
  let U := dominantRemainderSqNorm w i
  let target := dominantFourierCutoffMass A
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAReal : (0 : ℝ) < A := by exact_mod_cast hA
  have hmassReal : (651 : ℝ) * A ^ 2 ≤ (1000 : ℝ) * U := by
    dsimp [dominantResidualRatio] at hhigh
    have hA2 : (0 : ℝ) < (A : ℝ) ^ 2 := sq_pos_of_pos hAReal
    have hmul := (le_div_iff₀ hA2).mp hhigh
    norm_num [dominantThresholdFourierCutoff] at hmul ⊢
    nlinarith
  have hmass : 651 * A ^ 2 ≤ 1000 * U := by exact_mod_cast hmassReal
  have htargetPositive : 0 < target := by
    dsimp [target]
    have hcutoffLower : 651 * A ^ 2 ≤
        1000 * dominantFourierCutoffMass A := by
      have hceil := le_smul_ceilDiv (by norm_num : (0 : ℕ) < 1000)
        (b := 651 * A ^ 2)
      rw [Nat.nsmul_eq_mul] at hceil
      exact hceil
    have hA2 : 0 < A ^ 2 := pow_pos hA _
    omega
  have htargetTotal : target ≤ U := by
    dsimp [target, dominantFourierCutoffMass]
    exact (ceilDiv_le_iff_le_mul (by norm_num : (0 : ℕ) < 1000)).2 hmass
  have htargetLower : 651 * A ^ 2 ≤ 1000 * target := by
    dsimp [target, dominantFourierCutoffMass]
    have hceil := le_smul_ceilDiv (by norm_num : (0 : ℕ) < 1000)
      (b := 651 * A ^ 2)
    rw [Nat.nsmul_eq_mul] at hceil
    exact hceil
  let n := Fintype.card (DominantRemainderIndex i)
  let v : Fin n → ℤ := dominantRemainderFinWeights w i
  have hcap : ∀ j, (v j).natAbs ^ 2 ≤ A ^ 2 := by
    intro j
    exact dominantRemainderFinWeights_sq_le_amplitude_sq_of_maximal
      w i hmax j
  have htotal : target ≤ ∑ j, (v j).natAbs ^ 2 := by
    change target ≤ sqNorm v
    dsimp [v, n, U]
    rw [sqNorm_dominantRemainderFinWeights]
    exact htargetTotal
  obtain ⟨support, hlower, hupper⟩ :=
    exists_subset_sum_ge_lt_add_cap n target (A ^ 2)
      (fun j => (v j).natAbs ^ 2) htargetPositive hcap htotal
  have hsquare :
      sqNorm (fun j => if j ∈ support then v j else 0) =
        ∑ j ∈ support, (v j).natAbs ^ 2 := by
    unfold sqNorm
    calc
      ∑ j, (if j ∈ support then v j else 0).natAbs ^ 2 =
          ∑ j, if j ∈ support then (v j).natAbs ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ support <;> simp [hj]
      _ = ∑ j ∈ support, (v j).natAbs ^ 2 := by
        rw [← Finset.sum_filter]
        simp
  refine ⟨support, ?_, ?_⟩
  · rw [hsquare]
    exact htargetLower.trans (Nat.mul_le_mul_left 1000 hlower)
  · simpa [v, n, target, A, hsquare] using hupper

/-- After fixing the dominant activity bit, the exact conditional row kernel
is a canonically reindexed balanced-ternary residual row with shift `0` or
the nonnegative dominant amplitude. -/
theorem dominantConditionalRow_integral_eq_shiftedRemainder
    {d q : ℕ} (w : Fin d → ℤ) (i : Fin d) (activity : Bool)
    (s : ℝ) (hq : Odd q) :
    (∫ row, Real.exp (-s *
        (centeredMod q (∑ j, row j * w j) : ℝ) ^ 2)
        ∂(dominantConditionalRowPMF i activity).toMeasure) =
      ∫ row, Real.exp (-s *
        (centeredMod q
          ((if activity then (dominantAmplitude w i : ℤ) else 0) +
            ∑ j, row j * dominantRemainderFinWeights w i j) : ℝ) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure := by
  let X : (Fin d → ℤ) → ℤ := fun row => ∑ j, row j * w j
  let shift : ℤ := if activity then (dominantAmplitude w i : ℤ) else 0
  let Y : (DominantRemainderIndex i → Bool × Bool) → ℤ := fun seed =>
    shift + dominantRemainderRowSeedDot seed w
  let Z :
      (Fin (Fintype.card (DominantRemainderIndex i)) → ℤ) → ℤ := fun row =>
    shift + ∑ j, row j * dominantRemainderFinWeights w i j
  let f : ℤ → ℝ := fun t =>
    Real.exp (-s * (centeredMod q t : ℝ) ^ 2)
  have hf_even : Function.Even f := by
    intro t
    dsimp [f]
    rw [thresholdCenteredMod_neg hq]
    push_cast
    congr 1
    ring
  have hactual_uniform :
      ∫ row, f (X row) ∂(dominantConditionalRowPMF i activity).toMeasure =
        ∫ seed, f (Y seed)
          ∂(PMF.uniformOfFintype
            (DominantRemainderIndex i → Bool × Bool)).toMeasure := by
    cases activity
    · have hmap := dominantConditionalRowPMF_inactive_dot i w
      apply thresholdIntegral_comp_eq_of_pmf_map_eq
        (dominantConditionalRowPMF i false)
        (PMF.uniformOfFintype
          (DominantRemainderIndex i → Bool × Bool))
        X Y f (measurable_of_countable _) (measurable_of_countable _)
          (measurable_of_countable _)
      simpa [X, Y, shift] using hmap
    · apply thresholdIntegral_even_comp_eq_of_square_map_eq
      · exact hf_even
      · simpa [X, Y, shift] using
          dominantConditionalRowPMF_active_square_dot i w
  have hmap_reindex :
      (PMF.uniformOfFintype
        (DominantRemainderIndex i → Bool × Bool)).map Y =
      (sparseRademacherRow
        (Fintype.card (DominantRemainderIndex i))).map Z := by
    calc
      _ = (PMF.uniformOfFintype
          (DominantRemainderIndex i → Bool × Bool)).map
            (fun seed => Z (sparseRow
              (dominantRemainderRowSeedEquivFin i seed))) := by
        congr 1
        funext seed
        dsimp [Y, Z]
        rw [dominantRemainderRowSeedDot_eq_fin]
        rfl
      _ = ((PMF.uniformOfFintype
          (DominantRemainderIndex i → Bool × Bool)).map
            (fun seed => sparseRow
              (dominantRemainderRowSeedEquivFin i seed))).map Z := by
        rw [PMF.map_comp]
        rfl
      _ = (sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).map Z := by
        rw [map_uniformDominantRemainderRowSeed_reindex]
  have huniform_reindex :
      ∫ seed, f (Y seed)
          ∂(PMF.uniformOfFintype
            (DominantRemainderIndex i → Bool × Bool)).toMeasure =
        ∫ row, f (Z row)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure := by
    exact thresholdIntegral_comp_eq_of_pmf_map_eq
      (PMF.uniformOfFintype (DominantRemainderIndex i → Bool × Bool))
      (sparseRademacherRow (Fintype.card (DominantRemainderIndex i)))
      Y Z f (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _) hmap_reindex
  calc
    (∫ row, Real.exp (-s *
        (centeredMod q (∑ j, row j * w j) : ℝ) ^ 2)
        ∂(dominantConditionalRowPMF i activity).toMeasure) =
        ∫ row, f (X row)
          ∂(dominantConditionalRowPMF i activity).toMeasure := by rfl
    _ = ∫ seed, f (Y seed)
          ∂(PMF.uniformOfFintype
            (DominantRemainderIndex i → Bool × Bool)).toMeasure :=
      hactual_uniform
    _ = ∫ row, f (Z row)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure :=
      huniform_reindex
    _ = ∫ row, Real.exp (-s *
        (centeredMod q
          ((if activity then (dominantAmplitude w i : ℤ) else 0) +
            ∑ j, row j * dominantRemainderFinWeights w i j) : ℝ) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure := by rfl

/-- The sparse-row sine transform vanishes by symmetry. -/
theorem sparseRow_sineTransform (d : ℕ) (u : ℝ) (a : Fin d → ℝ) :
    ∫ row, Real.sin (u * realRowDot row a)
        ∂(sparseRademacherRow d).toMeasure = 0 := by
  have h_int :
      Integrable (fun row : Fin d → ℤ =>
        Complex.exp (u * realRowDot row a * Complex.I))
        (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (measurable_of_countable
        (fun row : Fin d → ℤ =>
          Complex.exp (u * realRowDot row a * Complex.I))).aestronglyMeasurable
    · filter_upwards with row
      simpa only [Complex.ofReal_mul] using
        (Complex.norm_exp_ofReal_mul_I (u * realRowDot row a)).le
  have h_im := integral_im h_int
  calc
    ∫ row, Real.sin (u * realRowDot row a)
        ∂(sparseRademacherRow d).toMeasure =
        ∫ row, (Complex.exp
          (u * realRowDot row a * Complex.I)).im
          ∂(sparseRademacherRow d).toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with row
      simpa only [Complex.ofReal_mul] using
        (Complex.exp_ofReal_mul_I_im (u * realRowDot row a)).symm
    _ = (∫ row, Complex.exp
          (u * realRowDot row a * Complex.I)
          ∂(sparseRademacherRow d).toMeasure).im := by
      rw [← RCLike.im_eq_complex_im]
      exact h_im
    _ = (∏ i, ((1 + Real.cos (u * a i)) / 2 : ℂ)).im := by
      rw [sparseRow_char]
    _ = 0 := by
      norm_cast

/-- A fixed real shift contributes exactly one cosine phase to the sparse
row transform. -/
theorem sparseRow_shiftedCosineTransform
    (d : ℕ) (u shift : ℝ) (a : Fin d → ℝ) :
    ∫ row, Real.cos (u * (shift + realRowDot row a))
        ∂(sparseRademacherRow d).toMeasure =
      Real.cos (u * shift) *
        ∏ i, (1 + Real.cos (u * a i)) / 2 := by
  have hcos : Integrable
      (fun row : Fin d → ℤ => Real.cos (u * realRowDot row a))
      (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    simpa only [Real.norm_eq_abs] using
      Real.abs_cos_le_one (u * realRowDot row a)
  have hsin : Integrable
      (fun row : Fin d → ℤ => Real.sin (u * realRowDot row a))
      (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    simpa only [Real.norm_eq_abs] using
      Real.abs_sin_le_one (u * realRowDot row a)
  calc
    ∫ row, Real.cos (u * (shift + realRowDot row a))
        ∂(sparseRademacherRow d).toMeasure =
        ∫ row,
          Real.cos (u * shift) * Real.cos (u * realRowDot row a) -
            Real.sin (u * shift) * Real.sin (u * realRowDot row a)
          ∂(sparseRademacherRow d).toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with row
      rw [show u * (shift + realRowDot row a) =
        u * shift + u * realRowDot row a by ring, Real.cos_add]
    _ = Real.cos (u * shift) *
          (∫ row, Real.cos (u * realRowDot row a)
            ∂(sparseRademacherRow d).toMeasure) -
        Real.sin (u * shift) *
          (∫ row, Real.sin (u * realRowDot row a)
            ∂(sparseRademacherRow d).toMeasure) := by
      rw [integral_sub (hcos.const_mul _) (hsin.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = Real.cos (u * shift) *
        ∏ i, (1 + Real.cos (u * a i)) / 2 := by
      rw [sparseRow_cosineTransform, sparseRow_sineTransform]
      ring

/-- A shifted cyclic mode before discarding its possibly negative phase. -/
noncomputable def shiftedSparseCyclicCosineMode
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ) (k : ℕ) : ℝ :=
  Real.cos ((2 * Real.pi * k / (q : ℝ)) * (shift : ℝ)) *
    sparseCyclicCosineMode q w k

/-- The upper-envelope mode obtained by discarding a negative shift phase. -/
noncomputable def nonnegativeShiftedSparseCyclicCosineMode
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ) (k : ℕ) : ℝ :=
  max 0 (Real.cos ((2 * Real.pi * k / (q : ℝ)) * (shift : ℝ))) *
    sparseCyclicCosineMode q w k

/-- Exact evaluation of a cosine polynomial under a shifted sparse row. -/
theorem sparseRow_shiftedCyclicCosinePolynomial
    (q d degree : ℕ) (shift : ℤ) (w : Fin d → ℤ)
    (coeff : Fin (degree + 1) → ℝ) :
    ∫ row, cyclicCosinePolynomial q coeff
        (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure =
      ∑ k, coeff k *
        shiftedSparseCyclicCosineMode q shift w (k : ℕ) := by
  unfold cyclicCosinePolynomial
  have hcos (k : Fin (degree + 1)) : Integrable
      (fun row : Fin d → ℤ => Real.cos
        ((2 * Real.pi * (k : ℕ) / (q : ℝ)) *
          ((shift + ∑ i, row i * w i : ℤ) : ℝ)))
      (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one
      ((2 * Real.pi * (k : ℕ) / (q : ℝ)) *
        ((shift + ∑ i, row i * w i : ℤ) : ℝ))
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    congr 1
    have hshifted := sparseRow_shiftedCosineTransform d
      (2 * Real.pi * (k : ℕ) / (q : ℝ)) (shift : ℝ)
      (fun i => (w i : ℝ))
    unfold shiftedSparseCyclicCosineMode sparseCyclicCosineMode
    rw [← hshifted]
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    simp only [realRowDot, Int.cast_add, Int.cast_sum, Int.cast_mul]
  · intro k _
    exact (hcos k).const_mul (coeff k)

/-- Shifted modes are bounded by deleting residual coordinates after negative
phase factors have been discarded. -/
theorem shiftedSparseCyclicCosineMode_le_nonnegative_restrict
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ)
    (support : Finset (Fin d)) (k : ℕ) :
    shiftedSparseCyclicCosineMode q shift w k ≤
      nonnegativeShiftedSparseCyclicCosineMode q shift
        (fun i => if i ∈ support then w i else 0) k := by
  let phase := Real.cos ((2 * Real.pi * k / (q : ℝ)) * (shift : ℝ))
  by_cases hphase : 0 ≤ phase
  · rw [shiftedSparseCyclicCosineMode,
      nonnegativeShiftedSparseCyclicCosineMode, max_eq_right hphase]
    exact mul_le_mul_of_nonneg_left
      (sparseCyclicCosineMode_le_restrict q w support k) hphase
  · rw [shiftedSparseCyclicCosineMode,
      nonnegativeShiftedSparseCyclicCosineMode,
      max_eq_left (le_of_not_ge hphase)]
    simp only [zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hphase)
      (sparseCyclicCosineMode_nonneg q w k)

/-- A positive Fourier majorant for a shifted row is controlled by a compact
residual subprofile.  The right side contains only nonnegative shift phases. -/
theorem sparseRow_shifted_le_cyclicCosineMajorant_restrict
    (q d degree : ℕ) (shift : ℤ) (w : Fin d → ℤ)
    (support : Finset (Fin d)) (s : ℝ)
    (coeff : Fin (degree + 1) → ℝ)
    (hs : 0 ≤ s) (hcoeff : ∀ k, 0 ≤ coeff k)
    (hmajorant : ∀ z : ℤ,
      Real.exp (-s * (centeredMod q z : ℝ) ^ 2) ≤
        cyclicCosinePolynomial q coeff z) :
    ∫ row, Real.exp (-s *
        (centeredMod q (shift + ∑ i, row i * w i) : ℝ) ^ 2)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∑ k, coeff k *
        nonnegativeShiftedSparseCyclicCosineMode q shift
          (fun i => if i ∈ support then w i else 0) (k : ℕ) := by
  have hleft : Integrable
      (fun row : Fin d → ℤ => Real.exp (-s *
        (centeredMod q (shift + ∑ i, row i * w i) : ℝ) ^ 2))
      (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _))
  have hright : Integrable
      (fun row : Fin d → ℤ => cyclicCosinePolynomial q coeff
        (shift + ∑ i, row i * w i))
      (sparseRademacherRow d).toMeasure := by
    unfold cyclicCosinePolynomial
    apply integrable_finsetSum Finset.univ
    intro k _
    refine (integrable_const (|coeff k| : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg (coeff k))
  calc
    ∫ row, Real.exp (-s *
        (centeredMod q (shift + ∑ i, row i * w i) : ℝ) ^ 2)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∫ row, cyclicCosinePolynomial q coeff
        (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure := by
      apply integral_mono_ae hleft hright
      filter_upwards [] with row
      exact hmajorant _
    _ = ∑ k, coeff k *
        shiftedSparseCyclicCosineMode q shift w (k : ℕ) :=
      sparseRow_shiftedCyclicCosinePolynomial q d degree shift w coeff
    _ ≤ ∑ k, coeff k *
        nonnegativeShiftedSparseCyclicCosineMode q shift
          (fun i => if i ∈ support then w i else 0) (k : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (shiftedSparseCyclicCosineMode_le_nonnegative_restrict
          q shift w support (k : ℕ)) (hcoeff k)

end CertifiedJL
