/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.GaussianFourier
import CertifiedJL.Projection.L2.Lower.BalancedTernary.LowerRowKernel

/-!
# Positive Fourier majorants for sparse protocol thresholds

A nonnegative cosine majorant of the centered modular Gaussian has an exact
sparse-row expectation: every frequency factors into one number in `[0,1]`
per coordinate.  Consequently adding coordinates can only decrease the
majorant expectation.  This is the dimension-free reduction needed to replace
an arbitrary high-norm input by a compact subprofile near the public threshold.

The module is purely semantic.  It does not choose a degree or contain
numeric certificate data.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

/-- A finite cosine polynomial evaluated on the cyclic angle associated with
an integer `z` modulo `q`. -/
noncomputable def cyclicCosinePolynomial
    (q : ℕ) {degree : ℕ} (coeff : Fin (degree + 1) → ℝ) (z : ℤ) : ℝ :=
  ∑ k, coeff k * Real.cos
    ((2 * Real.pi * (k : ℕ) / (q : ℝ)) * (z : ℝ))

/-- The exact sparse characteristic factor at one cyclic frequency. -/
noncomputable def sparseCyclicCosineMode
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (k : ℕ) : ℝ :=
  ∏ i, (1 + Real.cos
    ((2 * Real.pi * k / (q : ℝ)) * (w i : ℝ))) / 2

theorem sparseCyclicCosineMode_nonneg
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (k : ℕ) :
    0 ≤ sparseCyclicCosineMode q w k := by
  unfold sparseCyclicCosineMode
  apply Finset.prod_nonneg
  intro i _
  linarith [Real.neg_one_le_cos
    ((2 * Real.pi * k / (q : ℝ)) * (w i : ℝ))]

theorem sparseCyclicCosineMode_le_one
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (k : ℕ) :
    sparseCyclicCosineMode q w k ≤ 1 := by
  unfold sparseCyclicCosineMode
  apply Finset.prod_le_one
  · intro i _
    linarith [Real.neg_one_le_cos
      ((2 * Real.pi * k / (q : ℝ)) * (w i : ℝ))]
  · intro i _
    linarith [Real.cos_le_one
      ((2 * Real.pi * k / (q : ℝ)) * (w i : ℝ))]

/-- A finite family of nonnegative masses whose total crosses `target`
contains a subfamily that crosses it with overshoot smaller than one summand
cap.  This is the combinatorial half of the compact-subprofile reduction. -/
theorem exists_subset_sum_ge_lt_add_cap
    (dimension target cap : ℕ) (mass : Fin dimension → ℕ)
    (htarget : 0 < target) (hcap : ∀ i, mass i ≤ cap)
    (htotal : target ≤ ∑ i, mass i) :
    ∃ support : Finset (Fin dimension),
      target ≤ ∑ i ∈ support, mass i ∧
      ∑ i ∈ support, mass i < target + cap := by
  induction dimension with
  | zero =>
      simp at htotal
      omega
  | succ n ih =>
      let tail : Fin n → ℕ := fun i => mass i.succ
      by_cases hhead : target ≤ mass 0
      · refine ⟨{0}, ?_, ?_⟩
        · simpa using hhead
        · have := hcap 0
          simp only [Finset.sum_singleton]
          omega
      · have hhead_lt : mass 0 < target := Nat.lt_of_not_ge hhead
        by_cases htail : target ≤ ∑ i, tail i
        · obtain ⟨support, hlower, hupper⟩ :=
            ih tail (fun i => hcap i.succ) htail
          refine ⟨support.map (Fin.succEmb n), ?_, ?_⟩
          · simpa [tail] using hlower
          · simpa [tail] using hupper
        · refine ⟨Finset.univ, ?_, ?_⟩
          · simpa using htotal
          · have htail_lt : ∑ i, tail i < target := Nat.lt_of_not_ge htail
            have hhead_cap := hcap 0
            rw [Fin.sum_univ_succ]
            change mass 0 + ∑ i, tail i < target + cap
            omega

/-- If every coefficient is at most the public threshold and the vector norm
crosses that threshold, some coordinate subprofile has squared norm in the
compact band `[b^2, 2 b^2)`. -/
theorem exists_threshold_subprofile
    {d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hcoeff : ∀ i, (w i).natAbs ≤ inputThreshold) :
    ∃ support : Finset (Fin d),
      inputThreshold ^ 2 ≤
        sqNorm (fun i => if i ∈ support then w i else 0) ∧
      sqNorm (fun i => if i ∈ support then w i else 0) <
        2 * inputThreshold ^ 2 := by
  have htarget : 0 < inputThreshold ^ 2 := pow_pos hpositive _
  obtain ⟨support, hlower, hupper⟩ := exists_subset_sum_ge_lt_add_cap
    d (inputThreshold ^ 2) (inputThreshold ^ 2)
      (fun i => (w i).natAbs ^ 2) htarget
      (fun i => Nat.pow_le_pow_left (hcoeff i) 2) (by simpa [sqNorm] using hnorm)
  have hsquare :
      sqNorm (fun i => if i ∈ support then w i else 0) =
        ∑ i ∈ support, (w i).natAbs ^ 2 := by
    unfold sqNorm
    calc
      ∑ i, (if i ∈ support then w i else 0).natAbs ^ 2 =
          ∑ i, if i ∈ support then (w i).natAbs ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ support <;> simp [hi]
      _ = ∑ i ∈ support, (w i).natAbs ^ 2 := by
        rw [← Finset.sum_filter]
        simp
  refine ⟨support, ?_, ?_⟩
  · rw [hsquare]
    exact hlower
  · rw [hsquare, two_mul]
    exact hupper

/-- Under the diffuse `3/4` coordinate cap, the greedy subprofile has the
sharper overshoot bound `16 * ||v||² < 25 * b²`.  This replaces the generic
factor-two compact band by the exact `1 + (3/4)²` band seen by the analytic
certificate. -/
theorem exists_threshold_subprofile_of_three_quarters
    {d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hcoeff : ∀ i, 4 * (w i).natAbs ≤ 3 * inputThreshold) :
    ∃ support : Finset (Fin d),
      inputThreshold ^ 2 ≤
        sqNorm (fun i => if i ∈ support then w i else 0) ∧
      16 * sqNorm (fun i => if i ∈ support then w i else 0) <
        25 * inputThreshold ^ 2 := by
  let cap : ℕ := 9 * inputThreshold ^ 2 / 16
  have htarget : 0 < inputThreshold ^ 2 := pow_pos hpositive _
  have hmassCap : ∀ i, (w i).natAbs ^ 2 ≤ cap := by
    intro i
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
    have hi := hcoeff i
    have hsquare := Nat.pow_le_pow_left hi 2
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hsquare
  obtain ⟨support, hlower, hupper⟩ := exists_subset_sum_ge_lt_add_cap
    d (inputThreshold ^ 2) cap
      (fun i => (w i).natAbs ^ 2) htarget hmassCap
      (by simpa [sqNorm] using hnorm)
  have hsquare :
      sqNorm (fun i => if i ∈ support then w i else 0) =
        ∑ i ∈ support, (w i).natAbs ^ 2 := by
    unfold sqNorm
    calc
      ∑ i, (if i ∈ support then w i else 0).natAbs ^ 2 =
          ∑ i, if i ∈ support then (w i).natAbs ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ support <;> simp [hi]
      _ = ∑ i ∈ support, (w i).natAbs ^ 2 := by
        rw [← Finset.sum_filter]
        simp
  refine ⟨support, ?_, ?_⟩
  · rw [hsquare]
    exact hlower
  · rw [hsquare]
    dsimp [cap] at hupper
    omega

/-- A near-threshold coordinate can be retained while greedily truncating the
remaining squared mass.  The exact `49/50` cap gives the compact band
`2500 * ||v||² < 4901 * b²`.  This is the combinatorial reduction needed by
the near-dominant threshold certificate: unlike the generic greedy lemma, it
does not accidentally delete the coordinate that witnesses the branch. -/
theorem exists_threshold_subprofile_preserving_near
    {d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hcoeff : ∀ j, 50 * (w j).natAbs ≤ 49 * inputThreshold) :
    ∃ support : Finset (Fin d),
      i ∈ support ∧
      inputThreshold ^ 2 ≤
        sqNorm (fun j => if j ∈ support then w j else 0) ∧
      2500 * sqNorm (fun j => if j ∈ support then w j else 0) <
        4901 * inputThreshold ^ 2 := by
  have hd : d ≠ 0 := by
    intro hd
    subst d
    exact Fin.elim0 i
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  let amplitude : ℕ := (w i).natAbs
  let target : ℕ := inputThreshold ^ 2 - amplitude ^ 2
  let cap : ℕ := 2401 * inputThreshold ^ 2 / 2500
  let mass : Fin n → ℕ := fun j => (w (i.succAbove j)).natAbs ^ 2
  have hamplitude_lt : amplitude < inputThreshold := by
    dsimp [amplitude]
    have hi := hcoeff i
    omega
  have hamplitude_sq_lt : amplitude ^ 2 < inputThreshold ^ 2 :=
    Nat.pow_lt_pow_left hamplitude_lt (by norm_num)
  have htarget : 0 < target := by
    dsimp [target]
    omega
  have hmassCap : ∀ j, mass j ≤ cap := by
    intro j
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2500)).2
    have hj := hcoeff (i.succAbove j)
    have hsquare := Nat.pow_le_pow_left hj 2
    dsimp [mass, cap]
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hsquare
  have htotal : target ≤ ∑ j, mass j := by
    have hsum :
        sqNorm w = amplitude ^ 2 + ∑ j, mass j := by
      unfold sqNorm
      rw [Fin.sum_univ_succAbove (fun j => (w j).natAbs ^ 2) i]
    dsimp [target]
    rw [hsum] at hnorm
    omega
  obtain ⟨remainderSupport, hlower, hupper⟩ :=
    exists_subset_sum_ge_lt_add_cap n target cap mass
      htarget hmassCap htotal
  let support : Finset (Fin (n + 1)) :=
    insert i (remainderSupport.map i.succAboveEmb)
  have hi_support : i ∈ support := by simp [support]
  have hsquare :
      sqNorm (fun j => if j ∈ support then w j else 0) =
        amplitude ^ 2 + ∑ j ∈ remainderSupport, mass j := by
    unfold sqNorm
    rw [Fin.sum_univ_succAbove
      (fun j => (if j ∈ support then w j else 0).natAbs ^ 2) i]
    simp only [hi_support, ↓reduceIte]
    have hresidual :
        (∑ j, (if i.succAbove j ∈ support then
              w (i.succAbove j) else 0).natAbs ^ 2) =
          ∑ j ∈ remainderSupport, mass j := by
      calc
        _ = ∑ j, if j ∈ remainderSupport then mass j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j ∈ remainderSupport
          · have hmem : i.succAbove j ∈ support := by
              simp [support, hj]
            simp [hmem, hj, mass]
          · have hnotmem : i.succAbove j ∉ support := by
              simp [support, Fin.succAbove_ne, hj]
            simp [hnotmem, hj]
        _ = ∑ j ∈ remainderSupport, mass j := by
          rw [← Finset.sum_filter]
          simp
    rw [hresidual]
  refine ⟨support, hi_support, ?_, ?_⟩
  · rw [hsquare]
    have htarget_add : target + amplitude ^ 2 = inputThreshold ^ 2 :=
      Nat.sub_add_cancel (Nat.le_of_lt hamplitude_sq_lt)
    omega
  · rw [hsquare]
    have htarget_add : target + amplitude ^ 2 = inputThreshold ^ 2 :=
      Nat.sub_add_cancel (Nat.le_of_lt hamplitude_sq_lt)
    have hcap_mul : 2500 * cap ≤ 2401 * inputThreshold ^ 2 := by
      change 2500 * (2401 * inputThreshold ^ 2 / 2500) ≤
        2401 * inputThreshold ^ 2
      calc
        2500 * (2401 * inputThreshold ^ 2 / 2500) =
            (2401 * inputThreshold ^ 2 / 2500) * 2500 := by omega
        _ ≤ 2401 * inputThreshold ^ 2 :=
          Nat.div_mul_le_self (2401 * inputThreshold ^ 2) 2500
    omega

/-- Exact evaluation of a cosine polynomial under one sparse row. -/
theorem sparseRow_cyclicCosinePolynomial
    (q d degree : ℕ) (w : Fin d → ℤ)
    (coeff : Fin (degree + 1) → ℝ) :
    ∫ row, cyclicCosinePolynomial q coeff (∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure =
      ∑ k, coeff k * sparseCyclicCosineMode q w (k : ℕ) := by
  unfold cyclicCosinePolynomial
  have hcos (k : Fin (degree + 1)) : Integrable
      (fun row : Fin d → ℤ => Real.cos
        ((2 * Real.pi * (k : ℕ) / (q : ℝ)) *
          (∑ i, row i * w i : ℤ)))
      (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one
      ((2 * Real.pi * (k : ℕ) / (q : ℝ)) *
        (∑ i, row i * w i : ℤ))
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    congr 1
    have hfourier := sparseRow_cosineTransform d
      (2 * Real.pi * (k : ℕ) / (q : ℝ))
      (fun i => (w i : ℝ))
    unfold sparseCyclicCosineMode
    rw [← hfourier]
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    simp only [realRowDot, Int.cast_sum, Int.cast_mul]
  · intro k _
    exact (hcos k).const_mul (coeff k)

/-- A pointwise positive Fourier majorant transfers to the exact sparse-row
negative-Laplace transform. -/
theorem sparseRow_le_cyclicCosineMajorant
    (q d degree : ℕ) (w : Fin d → ℤ) (s : ℝ)
    (coeff : Fin (degree + 1) → ℝ)
    (hs : 0 ≤ s)
    (hmajorant : ∀ z : ℤ,
      Real.exp (-s * (centeredMod q z : ℝ) ^ 2) ≤
        cyclicCosinePolynomial q coeff z) :
    ∫ row, Real.exp (-s * sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∑ k, coeff k * sparseCyclicCosineMode q w (k : ℕ) := by
  have hleft : Integrable
      (fun row : Fin d → ℤ =>
        Real.exp (-s * sparseLowerRowKernel q w row))
      (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _))
  have hright : Integrable
      (fun row : Fin d → ℤ =>
        cyclicCosinePolynomial q coeff (∑ i, row i * w i))
      (sparseRademacherRow d).toMeasure := by
    unfold cyclicCosinePolynomial
    apply integrable_finsetSum Finset.univ
    intro k _
    have hcos : Integrable
        (fun row : Fin d → ℤ => Real.cos
          ((2 * Real.pi * (k : ℕ) / (q : ℝ)) *
            (∑ i, row i * w i : ℤ)))
        (sparseRademacherRow d).toMeasure := by
      refine (integrable_const (1 : ℝ)).mono'
        (measurable_of_countable _).aestronglyMeasurable ?_
      filter_upwards [] with row
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one
        ((2 * Real.pi * (k : ℕ) / (q : ℝ)) *
          (∑ i, row i * w i : ℤ))
    exact hcos.const_mul (coeff k)
  calc
    ∫ row, Real.exp (-s * sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∫ row, cyclicCosinePolynomial q coeff (∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure := by
      apply integral_mono_ae hleft hright
      filter_upwards [] with row
      simpa only [sparseLowerRowKernel_apply] using
        hmajorant (∑ i, row i * w i)
    _ = ∑ k, coeff k * sparseCyclicCosineMode q w (k : ℕ) :=
      sparseRow_cyclicCosinePolynomial q d degree w coeff

/-- Zeroing arbitrary coordinates can only increase each sparse cosine mode.
This is the exact algebraic form of the subprofile reduction. -/
theorem sparseCyclicCosineMode_le_restrict
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (support : Finset (Fin d)) (k : ℕ) :
    sparseCyclicCosineMode q w k ≤
      sparseCyclicCosineMode q
        (fun i => if i ∈ support then w i else 0) k := by
  unfold sparseCyclicCosineMode
  apply Finset.prod_le_prod
  · intro i _
    linarith [Real.neg_one_le_cos
      ((2 * Real.pi * k / (q : ℝ)) * (w i : ℝ))]
  · intro i _
    by_cases hi : i ∈ support
    · simp [hi]
    · simp [hi]
      linarith [Real.cos_le_one
        ((2 * Real.pi * k / (q : ℝ)) * (w i : ℝ))]

/-- A nonnegative positive-Fourier majorant for a subprofile bounds the full
row transform.  No dimension, norm, or ordering of coordinates appears in
the conclusion. -/
theorem sparseRow_le_cyclicCosineMajorant_restrict
    (q d degree : ℕ) (w : Fin d → ℤ) (support : Finset (Fin d)) (s : ℝ)
    (coeff : Fin (degree + 1) → ℝ)
    (hs : 0 ≤ s)
    (hcoeff : ∀ k, 0 ≤ coeff k)
    (hmajorant : ∀ z : ℤ,
      Real.exp (-s * (centeredMod q z : ℝ) ^ 2) ≤
        cyclicCosinePolynomial q coeff z) :
    ∫ row, Real.exp (-s * sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∑ k, coeff k * sparseCyclicCosineMode q
        (fun i => if i ∈ support then w i else 0) (k : ℕ) := by
  calc
    ∫ row, Real.exp (-s * sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∑ k, coeff k * sparseCyclicCosineMode q w (k : ℕ) :=
        sparseRow_le_cyclicCosineMajorant q d degree w s coeff hs hmajorant
    _ ≤ ∑ k, coeff k * sparseCyclicCosineMode q
        (fun i => if i ∈ support then w i else 0) (k : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (sparseCyclicCosineMode_le_restrict q w support (k : ℕ))
        (hcoeff k)

/-- Complete compact-subprofile reduction for a protocol threshold.  Under a
coordinate cap by `inputThreshold`, an arbitrary input of norm at least that
threshold is reduced to a subprofile with squared norm below twice the
threshold squared.  The full row transform is bounded by the positive Fourier
majorant evaluated only on that subprofile. -/
theorem sparseThresholdRow_le_compactSubprofileMajorant
    (q d degree : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ) (s : ℝ)
    (coeff : Fin (degree + 1) → ℝ)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hcoordinate : ∀ i, (w i).natAbs ≤ inputThreshold)
    (hs : 0 ≤ s) (hcoeff : ∀ k, 0 ≤ coeff k)
    (hmajorant : ∀ z : ℤ,
      Real.exp (-s * (centeredMod q z : ℝ) ^ 2) ≤
        cyclicCosinePolynomial q coeff z) :
    ∃ support : Finset (Fin d),
      inputThreshold ^ 2 ≤
          sqNorm (fun i => if i ∈ support then w i else 0) ∧
        sqNorm (fun i => if i ∈ support then w i else 0) <
          2 * inputThreshold ^ 2 ∧
        ∫ row, Real.exp (-s * sparseLowerRowKernel q w row)
            ∂(sparseRademacherRow d).toMeasure ≤
          ∑ k, coeff k * sparseCyclicCosineMode q
            (fun i => if i ∈ support then w i else 0) (k : ℕ) := by
  obtain ⟨support, hlower, hupper⟩ := exists_threshold_subprofile
    w inputThreshold hpositive hnorm hcoordinate
  exact ⟨support, hlower, hupper,
    sparseRow_le_cyclicCosineMajorant_restrict
      q d degree w support s coeff hs hcoeff hmajorant⟩

end CertifiedJL
