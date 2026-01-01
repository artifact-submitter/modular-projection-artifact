/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.Peano.PeanoMoments
import CertifiedJL.Analysis.SmoothBounds.ScaledSmoothCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Concrete translated Peano cutoff remainders

This module fixes the actual B3 approximant shape used by the noncompact
fourth-order bridge.  The cutoff is translated by the expansion point, so
`g n (x + y)` is literally `χₙ(y)` times the Taylor remainder in `y`.
The law-limit and stop-loss dominated-convergence proofs remain separate.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace CertifiedJL

/-- The standard Rademacher comparison law is kept as a concrete probability
   measure so the finite-support side of the cutoff bridge has an explicit
   owner, rather than an unnamed law premise. -/
noncomputable def standardRademacherMeasure : Measure ℝ :=
  (2 : ENNReal)⁻¹ • Measure.dirac (-1 : ℝ) +
    (2 : ENNReal)⁻¹ • Measure.dirac (1 : ℝ)

/-- The explicit two-point law is normalized before it is used as a
    Rademacher comparison measure. -/
instance standardRademacherMeasure_isProbabilityMeasure :
    IsProbabilityMeasure standardRademacherMeasure := by
  constructor
  rw [standardRademacherMeasure]
  simp [ENNReal.inv_two_add_inv_two]

noncomputable def upperCutoffRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x z : ℝ) : E :=
  upperCutoff n (z - x) •
    (f z - taylorPolynomial3 f x (z - x))

theorem upperCutoffRemainder_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x y : ℝ) :
    upperCutoffRemainder n f x (x + y) =
      upperCutoff n y • (f (x + y) - taylorPolynomial3 f x y) := by
  simp only [upperCutoffRemainder, add_sub_cancel_left]

theorem upperCutoffRemainder_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 4 f) (n : ℕ) (x : ℝ) :
    ContDiff ℝ 4 (upperCutoffRemainder n f x) := by
  have hshift : ContDiff ℝ 4 (fun z : ℝ => z - x) := by
    fun_prop
  have hcut : ContDiff ℝ 4 (fun z : ℝ => upperCutoff n (z - x)) :=
    (upperCutoff_contDiff n).comp hshift
  have hpoly : ContDiff ℝ 4
      (fun z : ℝ => taylorPolynomial3 f x (z - x)) := by
    simp only [taylorPolynomial3]
    fun_prop
  exact hcut.smul (hf.sub hpoly)

theorem upperCutoffRemainder_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x : ℝ) :
    HasCompactSupport (upperCutoffRemainder n f x) := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨Icc (x - 2 * upperCutoffRadius n) (x + 2 * upperCutoffRadius n),
    isCompact_Icc, ?_⟩
  intro z hz
  have hz' : z < x - 2 * upperCutoffRadius n ∨
      x + 2 * upperCutoffRadius n < z := by
    rw [mem_Icc] at hz
    by_cases hleft : z < x - 2 * upperCutoffRadius n
    · exact Or.inl hleft
    · right
      by_contra hright
      exact hz ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
  rcases hz' with hz' | hz'
  · have hnonpos : z - x ≤ 0 := by
      linarith [upperCutoffRadius_pos n]
    have habs : 2 * upperCutoffRadius n ≤ |z - x| := by
      rw [abs_of_nonpos hnonpos]
      linarith
    rw [upperCutoffRemainder, upperCutoff_eq_zero habs, zero_smul]
  · have hnonneg : 0 ≤ z - x := by
      linarith [upperCutoffRadius_pos n]
    have habs : 2 * upperCutoffRadius n ≤ |z - x| := by
      rw [abs_of_nonneg hnonneg]
      linarith
    rw [upperCutoffRemainder, upperCutoff_eq_zero habs, zero_smul]

/-- The translated compact approximants converge in Bochner integral to the
    uncut Taylor remainder under any real law for which that remainder is
    integrable. -/
theorem upperCutoffRemainder_integral_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure ℝ}
    {f : ℝ → E} (hf : ContDiff ℝ 4 f) (x : ℝ)
    (hrem : Integrable
      (fun y : ℝ => f (x + y) - taylorPolynomial3 f x y) μ) :
    Tendsto
      (fun n => ∫ y, upperCutoffRemainder n f x (x + y) ∂μ) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun y : ℝ => ‖f (x + y) - taylorPolynomial3 f x y‖) ?_ hrem.norm ?_ ?_
  · intro n
    have hgn : ContDiff ℝ 4
        (fun y : ℝ => upperCutoffRemainder n f x (x + y)) := by
      exact (upperCutoffRemainder_contDiff hf n x).comp (by fun_prop)
    exact hgn.continuous.aestronglyMeasurable
  · intro n
    filter_upwards [] with y
    rw [upperCutoffRemainder_apply, norm_smul]
    calc
      ‖(upperCutoff n y : ℝ)‖ *
          ‖f (x + y) - taylorPolynomial3 f x y‖ =
          upperCutoff n y *
            ‖f (x + y) - taylorPolynomial3 f x y‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (upperCutoff_nonneg n y)]
      _ ≤ 1 * ‖f (x + y) - taylorPolynomial3 f x y‖ := by
        exact mul_le_mul_of_nonneg_right (upperCutoff_le_one n y)
          (norm_nonneg _)
      _ = ‖f (x + y) - taylorPolynomial3 f x y‖ := one_mul _
  · filter_upwards [] with y
    simpa [upperCutoffRemainder_apply, one_smul] using
      (upperCutoff_pointwise_tendsto y).smul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => f (x + y) - taylorPolynomial3 f x y)
            atTop (𝓝 (f (x + y) - taylorPolynomial3 f x y)))

/-- The explicit two-point law discharges the generic remainder-integrability
    premise without imposing measurable-space structure on the codomain. -/
theorem upperCutoffRemainder_standardRademacher_integral_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E}
    (hf : ContDiff ℝ 4 f) (x : ℝ) :
    Tendsto
      (fun n => ∫ y, upperCutoffRemainder n f x (x + y)
        ∂standardRademacherMeasure) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y)
        ∂standardRademacherMeasure)) := by
  apply upperCutoffRemainder_integral_tendsto hf x
  rw [standardRademacherMeasure]
  apply Integrable.add_measure
  · exact (integrable_dirac
      (f := fun y : ℝ => f (x + y) - taylorPolynomial3 f x y)
      (a := (-1 : ℝ)) (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac
      (f := fun y : ℝ => f (x + y) - taylorPolynomial3 f x y)
      (a := (1 : ℝ)) (by simp)).smul_measure (by norm_num)

/-- The two support points lie in the unit core of every widened cutoff. -/
theorem upperCutoffRemainder_standardRademacher_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x : ℝ) :
    upperCutoffRemainder n f x (x + (-1 : ℝ)) =
        f (x + (-1 : ℝ)) - taylorPolynomial3 f x (-1 : ℝ) ∧
      upperCutoffRemainder n f x (x + (1 : ℝ)) =
        f (x + (1 : ℝ)) - taylorPolynomial3 f x (1 : ℝ) := by
  have hR : 1 ≤ upperCutoffRadius n := by
    dsimp [upperCutoffRadius]
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  constructor
  · rw [upperCutoffRemainder_apply, upperCutoff_eq_one]
    · simp
    · simpa using hR
  · rw [upperCutoffRemainder_apply, upperCutoff_eq_one]
    · simp
    · simpa using hR

/-- The exact fourth-order Leibniz expansion for the translated cutoff remainder.

The sum includes every cutoff derivative order `i = 0, ..., 4`; the later
pointwise-limit theorem identifies the zero-order cutoff term with the
uncut fourth derivative after separately cancelling the cubic Taylor term. -/
theorem upperCutoffRemainder_iteratedDeriv_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 4 f) (n : ℕ) (x z : ℝ) :
    iteratedDeriv 4 (upperCutoffRemainder n f x) z =
      ∑ i ∈ Finset.range (4 + 1),
        Nat.choose 4 i • iteratedDeriv i (fun z : ℝ => upperCutoff n (z - x)) z •
          iteratedDeriv (4 - i)
            (fun z : ℝ => f z - taylorPolynomial3 f x (z - x)) z := by
  have hshift : ContDiff ℝ 4 (fun z : ℝ => z - x) := by
    fun_prop
  have hcut : ContDiff ℝ 4
      (fun z : ℝ => upperCutoff n (z - x)) :=
    (upperCutoff_contDiff n).comp hshift
  have hpoly : ContDiff ℝ 4
      (fun z : ℝ => taylorPolynomial3 f x (z - x)) := by
    simp only [taylorPolynomial3]
    fun_prop
  have hrem : ContDiff ℝ 4
      (fun z : ℝ => f z - taylorPolynomial3 f x (z - x)) :=
    hf.sub hpoly
  change iteratedDeriv 4
      ((fun z : ℝ => upperCutoff n (z - x)) •
        (fun z : ℝ => f z - taylorPolynomial3 f x (z - x))) z = _
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_smul (Set.mem_univ z) uniqueDiffOn_univ
      hcut.contDiffWithinAt hrem.contDiffWithinAt

/-- A cutoff-radius-uniform envelope for every term in the fourth-order
Leibniz expansion of the translated remainder.

The constants depend only on the fixed smooth cutoff profile and the
derivative order.  In particular, they are independent of `n`, `x`, and `t`.
This is the cutoff-side estimate needed before the lower, middle, and upper
Taylor-remainder contributions can be dominated under the stop-loss weight. -/
theorem upperCutoffRemainder_iteratedDeriv_four_norm_le
    : ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        {f : ℝ → E}, ContDiff ℝ 4 f →
      ∀ (n : ℕ) (x t : ℝ),
        ‖iteratedDeriv 4 (upperCutoffRemainder n f x) (x + t)‖ ≤
          ∑ i ∈ Finset.range (4 + 1),
            Nat.choose 4 i * C i *
              ‖iteratedDeriv (4 - i)
                (fun z : ℝ => f z - taylorPolynomial3 f x (z - x))
                (x + t)‖ := by
  choose C hC using fun i => upperCutoff_iteratedDeriv_bound i
  have hC_nonneg (i : ℕ) : 0 ≤ C i := by
    have hbound := hC i 0 0
    have hpow : 0 < (upperCutoffRadius 0)⁻¹ ^ i :=
      pow_pos (inv_pos.mpr (upperCutoffRadius_pos 0)) i
    nlinarith [norm_nonneg (iteratedDeriv i (upperCutoff 0) 0)]
  refine ⟨C, hC_nonneg, ?_⟩
  intro E _ _ f hf n x t
  rw [upperCutoffRemainder_iteratedDeriv_four hf n x (x + t)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hshift :
      iteratedDeriv i (fun z : ℝ => upperCutoff n (z - x)) (x + t) =
        iteratedDeriv i (upperCutoff n) t := by
    have h := congrFun
      (iteratedDeriv_comp_sub_const i (upperCutoff n) x) (x + t)
    simpa only [add_sub_cancel_left] using h
  have hRadius : (1 : ℝ) ≤ upperCutoffRadius n := by
    simp [upperCutoffRadius]
  have hInv_nonneg : 0 ≤ (upperCutoffRadius n)⁻¹ :=
    inv_nonneg.mpr (upperCutoffRadius_pos n).le
  have hInv_le_one : (upperCutoffRadius n)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hRadius
  have hCutoff : ‖iteratedDeriv i (upperCutoff n) t‖ ≤ C i :=
    (hC i n t).trans
      (mul_le_of_le_one_right (hC_nonneg i)
        (pow_le_one₀ hInv_nonneg hInv_le_one))
  rw [hshift]
  calc
    ‖Nat.choose 4 i •
          (iteratedDeriv i (upperCutoff n) t •
            iteratedDeriv (4 - i)
              (fun z : ℝ => f z - taylorPolynomial3 f x (z - x))
              (x + t))‖
        ≤ Nat.choose 4 i *
            ‖iteratedDeriv i (upperCutoff n) t •
              iteratedDeriv (4 - i)
                (fun z : ℝ => f z - taylorPolynomial3 f x (z - x))
                (x + t)‖ :=
          norm_nsmul_le
    _ = (Nat.choose 4 i * ‖iteratedDeriv i (upperCutoff n) t‖) *
            ‖iteratedDeriv (4 - i)
              (fun z : ℝ => f z - taylorPolynomial3 f x (z - x))
              (x + t)‖ := by rw [norm_smul, mul_assoc]
    _ ≤ (Nat.choose 4 i * C i) *
          ‖iteratedDeriv (4 - i)
            (fun z : ℝ => f z - taylorPolynomial3 f x (z - x))
            (x + t)‖ := by
          gcongr
    _ = Nat.choose 4 i * C i *
          ‖iteratedDeriv (4 - i)
            (fun z : ℝ => f z - taylorPolynomial3 f x (z - x))
            (x + t)‖ := by rfl

theorem taylorPolynomial3_iteratedDeriv_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (x z : ℝ) :
    iteratedDeriv 4
      (fun y : ℝ => taylorPolynomial3 f x (y - x)) z = 0 := by
  have hterm (k : ℕ) (v : E) (hk : k ≤ 3) :
      iteratedDeriv 4 (fun y : ℝ => (y - x) ^ k • v) z = 0 := by
    rw [iteratedDeriv_smul_const (by fun_prop)]
    have hpow := congrFun
      (iteratedDeriv_comp_sub_const 4 (fun y : ℝ => y ^ k) x) z
    rw [hpow]
    simp [iteratedDeriv_pow, hk]
  have hterm2 (v : E) :
      iteratedDeriv 4 (fun y : ℝ => ((y - x) ^ 2 / 2) • v) z = 0 := by
    simpa [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      hterm 2 ((2 : ℝ)⁻¹ • v) (by norm_num)
  have hterm3 (v : E) :
      iteratedDeriv 4 (fun y : ℝ => ((y - x) ^ 3 / 6) • v) z = 0 := by
    simpa [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      hterm 3 ((6 : ℝ)⁻¹ • v) (by norm_num)
  let q0 : ℝ → E := fun y => (y - x) ^ 0 • f x
  let q1 : ℝ → E := fun y => (y - x) ^ 1 • deriv f x
  let q2 : ℝ → E := fun y => ((y - x) ^ 2 / 2) • deriv (deriv f) x
  let q3 : ℝ → E := fun y => ((y - x) ^ 3 / 6) • deriv (deriv (deriv f)) x
  simp only [taylorPolynomial3]
  change iteratedDeriv 4 (((q0 + q1) + q2) + q3) z = 0
  have hq0 : ContDiff ℝ 4 q0 := by
    dsimp [q0]
    fun_prop
  have hq1 : ContDiff ℝ 4 q1 := by
    dsimp [q1]
    fun_prop
  have hq2 : ContDiff ℝ 4 q2 := by
    dsimp [q2]
    fun_prop
  have hq3 : ContDiff ℝ 4 q3 := by
    dsimp [q3]
    fun_prop
  calc
    iteratedDeriv 4 (((q0 + q1) + q2) + q3) z =
        iteratedDeriv 4 ((q0 + q1) + q2) z + iteratedDeriv 4 q3 z :=
      iteratedDeriv_add ((hq0.add hq1).add hq2).contDiffAt hq3.contDiffAt
    _ = (iteratedDeriv 4 (q0 + q1) z + iteratedDeriv 4 q2 z) +
        iteratedDeriv 4 q3 z := by
      have h :
          iteratedDeriv 4 ((q0 + q1) + q2) z =
            iteratedDeriv 4 (q0 + q1) z + iteratedDeriv 4 q2 z :=
        iteratedDeriv_add (f := q0 + q1) (g := q2)
          (hq0.add hq1).contDiffAt hq2.contDiffAt
      rw [h]
    _ = ((iteratedDeriv 4 q0 z + iteratedDeriv 4 q1 z) +
        iteratedDeriv 4 q2 z) + iteratedDeriv 4 q3 z := by
      have h :
          iteratedDeriv 4 (q0 + q1) z =
            iteratedDeriv 4 q0 z + iteratedDeriv 4 q1 z :=
        iteratedDeriv_add (f := q0) (g := q1)
          hq0.contDiffAt hq1.contDiffAt
      rw [h]
    _ = 0 := by
      simp only [q0, q1, q2, q3,
        hterm 0 (f x) (by norm_num),
        hterm 1 (deriv f x) (by norm_num),
        hterm2 (deriv (deriv f) x),
        hterm3 (deriv (deriv (deriv f)) x), zero_add]

theorem upperCutoffRemainder_iteratedDeriv_four_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 4 f) (x t : ℝ) :
    Tendsto
      (fun n => iteratedDeriv 4 (upperCutoffRemainder n f x) (x + t)) atTop
      (𝓝 (iteratedDeriv 4 f (x + t))) := by
  obtain ⟨N, hNt⟩ := exists_nat_gt |t|
  have hEq :
      (fun n => iteratedDeriv 4 (upperCutoffRemainder n f x) (x + t)) =ᶠ[atTop]
        (fun _ => iteratedDeriv 4 f (x + t)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hNR : (N : ℝ) ≤ upperCutoffRadius n := by
      dsimp [upperCutoffRadius]
      linarith
    have htR : |t| < upperCutoffRadius n := lt_of_lt_of_le hNt hNR
    have heq : (fun y : ℝ => upperCutoff n (y - x)) =ᶠ[𝓝 (x + t)]
        (fun _ : ℝ => (1 : ℝ)) := by
      have hcont : ContinuousAt (fun y : ℝ => |y - x|) (x + t) := by
        fun_prop
      have htR' : |(x + t) - x| < upperCutoffRadius n := by
        simpa using htR
      filter_upwards [hcont.eventually (Iio_mem_nhds htR')] with y hy
      exact upperCutoff_eq_one (le_of_lt hy)
    have hderiv (i : ℕ) :
        iteratedDeriv i (fun y : ℝ => upperCutoff n (y - x)) (x + t) =
          iteratedDeriv i (fun _ : ℝ => (1 : ℝ)) (x + t) :=
      heq.iteratedDeriv_eq i
    have hpoly : ContDiff ℝ 4
        (fun y : ℝ => taylorPolynomial3 f x (y - x)) := by
      simp only [taylorPolynomial3]
      fun_prop
    have hrem :
        iteratedDeriv 4 (fun y : ℝ => f y - taylorPolynomial3 f x (y - x))
            (x + t) = iteratedDeriv 4 f (x + t) := by
      change iteratedDeriv 4
        (f - (fun y : ℝ => taylorPolynomial3 f x (y - x))) (x + t) = _
      rw [iteratedDeriv_sub hf.contDiffAt hpoly.contDiffAt]
      rw [taylorPolynomial3_iteratedDeriv_four]
      simp
    rw [upperCutoffRemainder_iteratedDeriv_four hf n x (x + t)]
    simp_rw [hderiv]
    simp [iteratedDeriv_const, hrem]
  exact (tendsto_congr' hEq).mpr tendsto_const_nhds

end CertifiedJL
