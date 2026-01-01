import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Intermediate.Modular
import CertifiedJL.Probability.Distributions.Gaussian.ShiftedGaussian

/-!
# Exact finite-PMF bridge for the intermediate sparse profile

This module isolates one sparse entry from an arbitrary coordinate of a sparse
row.  The resulting Fubini identity exposes the exact inactive and signed
entry masses used by the intermediate shifted-square estimate.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

/-- Integration against one sparse entry is the exact `1/4, 1/2, 1/4` mix. -/
theorem sparseEntry_integral_eq_mix (f : ℤ → ℝ) :
    ∫ z, f z ∂sparseEntryPMF.toMeasure =
      (1 / 4 : ℝ) * f (-1) + (1 / 2 : ℝ) * f 0 + (1 / 4 : ℝ) * f 1 := by
  rw [sparseEntryPMF]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (Bool × Bool)) (f := sparseBit)
    (measurable_of_finite sparseBit)]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite sparseBit)
    (measurable_of_countable f).stronglyMeasurable]
  rw [finitePMF_integral_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, sparseBit]
  ring

/--
Fubini splitting of an arbitrary coordinate of a sparse row into that entry
and the residual sparse row.
-/
theorem sparseRademacherRow_integral_split_coordinate {n : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℤ) → ℝ)
    (hf : Integrable f (sparseRademacherRow (n + 1)).toMeasure) :
    ∫ row, f row ∂(sparseRademacherRow (n + 1)).toMeasure =
      ∫ z, ∫ rest,
        f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℤ) i).symm
          (z, rest))
          ∂(sparseRademacherRow n).toMeasure
        ∂sparseEntryPMF.toMeasure := by
  rw [sparseRademacherRow_toMeasure] at hf ⊢
  let μ : Fin (n + 1) → Measure ℤ := fun _ ↦ sparseEntryPMF.toMeasure
  have he := measurePreserving_piFinSuccAbove μ i
  rw [← he.symm.integral_comp']
  rw [integral_prod]
  · simp only [μ]
    rw [← sparseRademacherRow_toMeasure]
  · exact he.symm.integrable_comp_of_integrable hf

/-- The coordinate split with the sparse entry integral evaluated exactly. -/
theorem sparseRademacherRow_integral_eq_mix_coordinate {n : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℤ) → ℝ)
    (hf : Integrable f (sparseRademacherRow (n + 1)).toMeasure) :
    ∫ row, f row ∂(sparseRademacherRow (n + 1)).toMeasure =
      (1 / 4 : ℝ) *
          (∫ rest, f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ ℤ) i).symm (-1, rest))
            ∂(sparseRademacherRow n).toMeasure) +
        (1 / 2 : ℝ) *
          (∫ rest, f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ ℤ) i).symm (0, rest))
            ∂(sparseRademacherRow n).toMeasure) +
        (1 / 4 : ℝ) *
          (∫ rest, f ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ ℤ) i).symm (1, rest))
            ∂(sparseRademacherRow n).toMeasure) := by
  rw [sparseRademacherRow_integral_split_coordinate i f hf]
  exact sparseEntry_integral_eq_mix _

/-- A selected coordinate exposes an arbitrary positive dimension in the
canonical successor form used by the coordinate-split theorems. -/
theorem exists_dimension_eq_succ_of_fin {d : ℕ} (i : Fin d) :
    ∃ n : ℕ, d = n + 1 := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
    intro h
    subst d
    exact Fin.elim0 i)
  exact ⟨d - 1, (Nat.sub_add_cancel hd).symm⟩

/-- Isolating one coordinate splits the real row dot product exactly. -/
theorem realRowDot_piFinSuccAbove_symm {n : ℕ} (i : Fin (n + 1))
    (z : ℤ) (rest : Fin n → ℤ) (a : Fin (n + 1) → ℝ) :
    realRowDot
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℤ) i).symm
          (z, rest)) a =
      (z : ℝ) * a i + realRowDot rest (fun j ↦ a (i.succAbove j)) := by
  rw [realRowDot, Fin.sum_univ_succAbove _ i]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

/--
The shifted-square exponential after an arbitrary coordinate split, with its
inactive and two signed images displayed explicitly.
-/
theorem sparseRow_shiftedSquare_integral_eq_mix_coordinate {n : ℕ}
    (i : Fin (n + 1)) (a : Fin (n + 1) → ℝ) (alpha shift : ℝ) :
    ∫ row, Real.exp (-alpha * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure =
      (1 / 4 : ℝ) *
          (∫ rest, Real.exp (-alpha *
            ((-1 : ℝ) * a i +
              realRowDot rest (fun j ↦ a (i.succAbove j)) - shift) ^ 2)
            ∂(sparseRademacherRow n).toMeasure) +
        (1 / 2 : ℝ) *
          (∫ rest, Real.exp (-alpha *
            (realRowDot rest (fun j ↦ a (i.succAbove j)) - shift) ^ 2)
            ∂(sparseRademacherRow n).toMeasure) +
        (1 / 4 : ℝ) *
          (∫ rest, Real.exp (-alpha *
            (a i + realRowDot rest (fun j ↦ a (i.succAbove j)) - shift) ^ 2)
            ∂(sparseRademacherRow n).toMeasure) := by
  have hint : Integrable
      (fun row ↦ Real.exp (-alpha * (realRowDot row a - shift) ^ 2))
      (sparseRademacherRow (n + 1)).toMeasure := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    rw [← PMF.toMeasure_map
      (p := PMF.uniformOfFintype (SparseRowSeed (n + 1)))
      (f := sparseRow) (measurable_of_finite sparseRow)]
    apply (integrable_map_measure
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_finite sparseRow).aemeasurable).2
    exact Integrable.of_finite
  rw [sparseRademacherRow_integral_eq_mix_coordinate i _ hint]
  simp_rw [realRowDot_piFinSuccAbove_symm]
  norm_num

/--
The sparse-row MGF bound with its exact squared-mass parameter exposed.
-/
theorem sparseRowMGF_subGaussian_mass {d : ℕ} (a : Fin d → ℝ) (t : ℝ) :
    ∫ row, Real.exp (t * realRowDot row a) ∂(sparseRademacherRow d).toMeasure ≤
      Real.exp ((∑ i, a i ^ 2) * t ^ 2 / 4) := by
  calc
    (∫ row, Real.exp (t * realRowDot row a) ∂(sparseRademacherRow d).toMeasure) =
        ∫ row, Real.exp (realRowDot row (fun i ↦ t * a i))
          ∂(sparseRademacherRow d).toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with row
      congr 1
      simp only [realRowDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∏ i, (1 + Real.cosh (t * a i)) / 2 := by
      simp only [sparseRowMGF]
    _ = ∏ i, Real.cosh (t * a i / 2) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      have harg : t * a i = 2 * (t * a i / 2) := by ring
      conv_lhs => rw [harg]
      rw [Real.cosh_two_mul, Real.cosh_sq]
      ring
    _ ≤ ∏ i, Real.exp ((t * a i) ^ 2 / 4) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hcosh := Real.cosh_le_exp_half_sq (t * a i / 2)
        have hsq := pow_le_pow_left₀ (Real.cosh_pos _).le hcosh 2
        calc
          Real.cosh (t * a i / 2) ^ 2 ≤
              Real.exp ((t * a i / 2) ^ 2 / 2) ^ 2 := hsq
          _ = Real.exp ((t * a i) ^ 2 / 4) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    _ = Real.exp ((∑ i, a i ^ 2) * t ^ 2 / 4) := by
      rw [← Real.exp_sum]
      congr 1
      rw [show (∑ i, a i ^ 2) * t ^ 2 / 4 =
        (∑ i, a i ^ 2) * (t ^ 2 / 4) by ring, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/--
The squared-mass sparse-row MGF gives the shifted Gaussian envelope needed
after one coordinate has been removed.
-/
theorem sparseRow_shiftedGaussianEnvelope {n : ℕ} (a : Fin n → ℝ)
    (alpha shift : ℝ) (halpha : 0 < alpha) :
    ∫ row, Real.exp (-alpha * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow n).toMeasure ≤
      Real.exp (-alpha * shift ^ 2 / (1 + alpha * ∑ i, a i ^ 2)) := by
  have hmass : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg (a i)
  have hbound := shiftedGaussianEnvelope
    (X := fun row ↦ realRowDot row a)
    (μ := (sparseRademacherRow n).toMeasure)
    (σ := Real.sqrt ((∑ i, a i ^ 2) / 2))
    (α := alpha) (a := shift)
    (hX_meas := measurable_of_countable _)
    (hX_int := by
      intro t
      rw [sparseRademacherRow_eq_map_uniformRowSeed]
      rw [← PMF.toMeasure_map
        (p := PMF.uniformOfFintype (SparseRowSeed n))
        (f := sparseRow) (measurable_of_finite sparseRow)]
      apply (integrable_map_measure
        (measurable_of_countable _).aestronglyMeasurable
        (measurable_of_finite sparseRow).aemeasurable).2
      exact Integrable.of_finite)
    (hmgf := by
      intro t
      convert sparseRowMGF_subGaussian_mass a t using 1
      congr 1
      rw [Real.sq_sqrt (div_nonneg hmass (by norm_num))]
      ring)
    (hα := halpha)
  convert hbound using 1
  congr 2
  rw [Real.sq_sqrt (div_nonneg hmass (by norm_num))]
  ring

/-- The exact coordinate mix followed by the residual shifted-Gaussian
envelope.  This is the one-image finite-PMF bridge used by L13. -/
theorem sparseRow_intermediate_image_le {n : ℕ} (i : Fin (n + 1))
    (a : Fin (n + 1) → ℝ) (r shift : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r) :
    ∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure ≤
      (1 / 4 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift + a i) ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * shift ^ 2) +
        (1 / 4 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift - a i) ^ 2) := by
  let b : Fin n → ℝ := fun j ↦ a (i.succAbove j)
  have hmass : ∑ j, b j ^ 2 = 1 - r := by
    rw [show (∑ j, b j ^ 2) = (∑ j, a (i.succAbove j) ^ 2) by rfl]
    rw [Fin.sum_univ_succAbove (fun j ↦ a j ^ 2) i] at hnorm
    linarith
  have hminus := sparseRow_shiftedGaussianEnvelope b (23 / 10)
    (shift + a i) (by norm_num)
  have hzero := sparseRow_shiftedGaussianEnvelope b (23 / 10)
    shift (by norm_num)
  have hplus := sparseRow_shiftedGaussianEnvelope b (23 / 10)
    (shift - a i) (by norm_num)
  rw [hmass] at hminus hzero hplus
  have henvelope (x : ℝ) :
      Real.exp (-(23 / 10 : ℝ) * x ^ 2 /
          (1 + (23 / 10 : ℝ) * (1 - r))) =
        Real.exp (-intermediateAlpha r * x ^ 2) := by
    rw [intermediateAlpha]
    congr 1
    ring
  rw [henvelope] at hminus hzero hplus
  have hminus' :
      (∫ rest, Real.exp (-(23 / 10 : ℝ) *
          (((-1 : ℝ) * a i + realRowDot rest (fun j ↦ a (i.succAbove j))) -
            shift) ^ 2) ∂(sparseRademacherRow n).toMeasure) ≤
        Real.exp (-intermediateAlpha r * (shift + a i) ^ 2) := by
    calc
      _ = ∫ rest, Real.exp (-(23 / 10 : ℝ) *
          (realRowDot rest b - (shift + a i)) ^ 2)
          ∂(sparseRademacherRow n).toMeasure := by
        apply integral_congr_ae
        filter_upwards [] with rest
        congr 1
        ring
      _ ≤ _ := hminus
  have hplus' :
      (∫ rest, Real.exp (-(23 / 10 : ℝ) *
          ((a i + realRowDot rest (fun j ↦ a (i.succAbove j))) - shift) ^ 2)
          ∂(sparseRademacherRow n).toMeasure) ≤
        Real.exp (-intermediateAlpha r * (shift - a i) ^ 2) := by
    calc
      _ = ∫ rest, Real.exp (-(23 / 10 : ℝ) *
          (realRowDot rest b - (shift - a i)) ^ 2)
          ∂(sparseRademacherRow n).toMeasure := by
        apply integral_congr_ae
        filter_upwards [] with rest
        congr 1
        ring
      _ ≤ _ := hplus
  rw [sparseRow_shiftedSquare_integral_eq_mix_coordinate i a (23 / 10) shift]
  dsimp only [b] at hzero
  linarith

/-- Pairing opposite modular images removes the sign of the selected
coefficient and produces exactly one L13 summand. -/
theorem sparseRow_intermediate_paired_images_le {n : ℕ} (i : Fin (n + 1))
    (a : Fin (n + 1) → ℝ) (r shift : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r) :
    (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure) +
      (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a + shift) ^ 2)
        ∂(sparseRademacherRow (n + 1)).toMeasure) ≤
      Real.exp (-intermediateAlpha r * shift ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift - Real.sqrt r) ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift + Real.sqrt r) ^ 2) := by
  have hpos := sparseRow_intermediate_image_le i a r shift hnorm hr
  have hneg := sparseRow_intermediate_image_le i a r (-shift) hnorm hr
  have hsqrt : Real.sqrt r = |a i| := by
    rw [← hr, Real.sqrt_sq_eq_abs]
  by_cases hai : 0 ≤ a i
  · rw [abs_of_nonneg hai] at hsqrt
    rw [hsqrt]
    calc
      _ = (∫ row, Real.exp (-(23 / 10 : ℝ) *
              (realRowDot row a - shift) ^ 2)
              ∂(sparseRademacherRow (n + 1)).toMeasure) +
            (∫ row, Real.exp (-(23 / 10 : ℝ) *
              (realRowDot row a - (-shift)) ^ 2)
              ∂(sparseRademacherRow (n + 1)).toMeasure) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with row
          congr 1
          ring
      _ ≤ _ := add_le_add hpos hneg
      _ = _ := by ring_nf
  · have hai' : a i < 0 := lt_of_not_ge hai
    rw [abs_of_neg hai'] at hsqrt
    rw [hsqrt]
    calc
      _ = (∫ row, Real.exp (-(23 / 10 : ℝ) *
              (realRowDot row a - shift) ^ 2)
              ∂(sparseRademacherRow (n + 1)).toMeasure) +
            (∫ row, Real.exp (-(23 / 10 : ℝ) *
              (realRowDot row a - (-shift)) ^ 2)
              ∂(sparseRademacherRow (n + 1)).toMeasure) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with row
          congr 1
          ring
      _ ≤ _ := add_le_add hpos hneg
      _ = _ := by ring_nf

/-- Consumer-facing form of the paired-image theorem for an arbitrary
dimension carrying a selected coordinate. -/
theorem sparseRow_intermediate_paired_images_le_of_fin {d : ℕ} (i : Fin d)
    (a : Fin d → ℝ) (r shift : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r) :
    (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a - shift) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) +
      (∫ row, Real.exp (-(23 / 10 : ℝ) * (realRowDot row a + shift) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) ≤
      Real.exp (-intermediateAlpha r * shift ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift - Real.sqrt r) ^ 2) +
        (1 / 2 : ℝ) * Real.exp
          (-intermediateAlpha r * (shift + Real.sqrt r) ^ 2) := by
  obtain ⟨n, rfl⟩ := exists_dimension_eq_succ_of_fin i
  exact sparseRow_intermediate_paired_images_le i a r shift hnorm hr

/-- Summing the paired nonzero modular images gives exactly L13. -/
theorem sparseRow_intermediate_nonzero_images_le_L13 {d : ℕ} (i : Fin d)
    (a : Fin d → ℝ) (r D : ℝ)
    (hnorm : ∑ j, a j ^ 2 = 1) (hr : a i ^ 2 = r)
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D) :
    (∑' n : ℕ, ((∫ row, Real.exp (-(23 / 10 : ℝ) *
          (realRowDot row a - ((n : ℝ) + 1) * D) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) +
        (∫ row, Real.exp (-(23 / 10 : ℝ) *
          (realRowDot row a + ((n : ℝ) + 1) * D) ^ 2)
          ∂(sparseRademacherRow d).toMeasure))) ≤
      intermediateL13 r D := by
  let f : ℕ → ℝ := fun n ↦
    (∫ row, Real.exp (-(23 / 10 : ℝ) *
        (realRowDot row a - ((n : ℝ) + 1) * D) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) +
      (∫ row, Real.exp (-(23 / 10 : ℝ) *
        (realRowDot row a + ((n : ℝ) + 1) * D) ^ 2)
        ∂(sparseRademacherRow d).toMeasure)
  let g : ℕ → ℝ := fun n ↦
    Real.exp (-intermediateAlpha r * (((n : ℝ) + 1) * D) ^ 2) +
      (1 / 2 : ℝ) * Real.exp (-intermediateAlpha r *
        (((n : ℝ) + 1) * D - Real.sqrt r) ^ 2) +
      (1 / 2 : ℝ) * Real.exp (-intermediateAlpha r *
        (((n : ℝ) + 1) * D + Real.sqrt r) ^ 2)
  obtain ⟨hzero, hminus, hplus⟩ :=
    intermediateL13_terms_summable hr0 hr1 hD
  have hg : Summable g := by
    exact (hzero.add (hminus.mul_left (1 / 2))).add
      (hplus.mul_left (1 / 2))
  have hfg (n : ℕ) : f n ≤ g n := by
    exact sparseRow_intermediate_paired_images_le_of_fin i a r
      (((n : ℝ) + 1) * D) hnorm hr
  have hf0 (n : ℕ) : 0 ≤ f n := by
    exact add_nonneg (integral_nonneg fun _ ↦ Real.exp_nonneg _)
      (integral_nonneg fun _ ↦ Real.exp_nonneg _)
  have hf : Summable f := hg.of_nonneg_of_le hf0 hfg
  have hsum : (∑' n : ℕ, f n) ≤ intermediateL13 r D := by
    calc
      (∑' n : ℕ, f n) ≤ ∑' n : ℕ, g n := hf.tsum_le_tsum hfg hg
      _ = intermediateL13 r D := by
        rw [Summable.tsum_add
          (hzero.add (hminus.mul_left (1 / 2))) (hplus.mul_left (1 / 2)),
          Summable.tsum_add hzero (hminus.mul_left (1 / 2)),
          tsum_mul_left, tsum_mul_left]
        simp only [intermediateL13]
  simpa only [f, Nat.cast_add, Nat.cast_one] using hsum

end CertifiedJL
