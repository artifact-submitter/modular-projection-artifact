/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Distributions.Gamma

/-!
# Integer-shape Gamma survival probabilities

This file isolates the exact finite arithmetic used by the sparse upper-tail
counterexample.  The analytic API is stated for every positive integer shape;
the concrete shape-`128` comparison is then discharged by a small
kernel-checked exponential enclosure and exact rational arithmetic.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace Probability

/-- The finite expression for the survival function of `Gamma(n, 1)`. -/
noncomputable def gammaSurvivalNat (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * ∑ k ∈ Finset.range n, x ^ k / k.factorial

/-- Derivative of the finite integer-shape survival expression. -/
theorem hasDerivAt_gammaSurvivalNat_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (gammaSurvivalNat (n + 1))
      (-Real.exp (-x) * x ^ n / n.factorial) x := by
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using
      (hasDerivAt_id x).neg.exp
  induction n with
  | zero =>
      rw [show gammaSurvivalNat (0 + 1) =
          fun y : ℝ => Real.exp (-y) by
        funext y
        simp [gammaSurvivalNat]]
      norm_num
      exact hexp
  | succ n ih =>
      have hterm :
          HasDerivAt
              (fun y : ℝ =>
                Real.exp (-y) * y ^ (n + 1) / (n + 1).factorial)
              (-Real.exp (-x) * x ^ (n + 1) / (n + 1).factorial +
                Real.exp (-x) * ((n + 1) * x ^ n) /
                  (n + 1).factorial) x := by
        apply
          (hexp.mul ((hasDerivAt_id x).pow (n + 1))).div_const
            ((n + 1).factorial : ℝ) |>.congr_deriv
        simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel]
        push_cast
        ring
      have hfun :
          gammaSurvivalNat (n + 1 + 1) =
            gammaSurvivalNat (n + 1) +
              fun y : ℝ =>
                Real.exp (-y) * y ^ (n + 1) / (n + 1).factorial := by
        funext y
        simp only [Pi.add_apply, gammaSurvivalNat,
          Finset.sum_range_succ]
        ring
      rw [hfun]
      apply (ih.add hterm).congr_deriv
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- The finite integer-shape survival expression tends to zero. -/
theorem tendsto_gammaSurvivalNat_atTop (n : ℕ) :
    Filter.Tendsto (gammaSurvivalNat n) Filter.atTop (nhds 0) := by
  unfold gammaSurvivalNat
  simp_rw [Finset.mul_sum]
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum
      (f := fun (k : ℕ) (x : ℝ) =>
        Real.exp (-x) * (x ^ k / k.factorial))
      (a := fun _ => 0) (Finset.range n) (fun k _ => by
        have hk :=
          (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul
            ((k.factorial : ℝ)⁻¹)
        have hk0 :
            Filter.Tendsto
              (fun y : ℝ =>
                (k.factorial : ℝ)⁻¹ *
                  (y ^ k * Real.exp (-y)))
              Filter.atTop (nhds 0) := by
          simpa using hk
        apply hk0.congr'
        filter_upwards with y
        field_simp))

/-- The upper incomplete-Gamma integral at an integer shape is a finite sum. -/
theorem integral_pow_mul_exp_neg_Ioi (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ y : ℝ in Set.Ioi x,
        Real.exp (-y) * y ^ n / n.factorial) =
      gammaSurvivalNat (n + 1) x := by
  let derivative : ℝ → ℝ :=
    fun y => -Real.exp (-y) * y ^ n / n.factorial
  have hderiv :
      ∀ y ∈ Set.Ici x,
        HasDerivAt (gammaSurvivalNat (n + 1)) (derivative y) y :=
    fun y _ => hasDerivAt_gammaSurvivalNat_succ n y
  have hnonpos : ∀ y ∈ Set.Ioi x, derivative y ≤ 0 := by
    intro y hy
    dsimp only [derivative]
    have hy0 : 0 ≤ y := hx.trans hy.le
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Real.exp_nonneg _)) (pow_nonneg hy0 _))
      (by positivity)
  have hintegral :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos'
      hderiv hnonpos (tendsto_gammaSurvivalNat_atTop (n + 1))
  have hneg :
      (∫ y : ℝ in Set.Ioi x, derivative y) =
        -(∫ y : ℝ in Set.Ioi x,
            Real.exp (-y) * y ^ n / n.factorial) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only [derivative]
    ring
  rw [hneg, zero_sub] at hintegral
  exact neg_inj.mp hintegral

/-- Integrability companion to `integral_pow_mul_exp_neg_Ioi`. -/
theorem integrableOn_pow_mul_exp_neg_Ioi (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn
      (fun y : ℝ => Real.exp (-y) * y ^ n / n.factorial)
      (Set.Ioi x) := by
  let derivative : ℝ → ℝ :=
    fun y => -Real.exp (-y) * y ^ n / n.factorial
  have hderiv :
      ∀ y ∈ Set.Ici x,
        HasDerivAt (gammaSurvivalNat (n + 1)) (derivative y) y :=
    fun y _ => hasDerivAt_gammaSurvivalNat_succ n y
  have hnonpos : ∀ y ∈ Set.Ioi x, derivative y ≤ 0 := by
    intro y hy
    dsimp only [derivative]
    have hy0 : 0 ≤ y := hx.trans hy.le
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Real.exp_nonneg _)) (pow_nonneg hy0 _))
      (by positivity)
  have hderivative :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'
      hderiv hnonpos (tendsto_gammaSurvivalNat_atTop (n + 1))
  exact hderivative.neg.congr_fun (fun y _ => by
    simp only [Pi.neg_apply]
    dsimp only [derivative]
    ring) measurableSet_Ioi

/-- Exact survival formula for every positive integer-shape unit-rate Gamma law. -/
theorem gammaMeasure_Ioi_nat (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gammaMeasure (n + 1) 1 (Set.Ioi x) =
      ENNReal.ofReal (gammaSurvivalNat (n + 1) x) := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Ioi]
  have hintegrable :=
    integrableOn_pow_mul_exp_neg_Ioi n hx
  have hpdf :
      (∫⁻ y : ℝ in Set.Ioi x, gammaPDF (n + 1) 1 y) =
        ∫⁻ y : ℝ in Set.Ioi x,
          ENNReal.ofReal
            (Real.exp (-y) * y ^ n / n.factorial) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : 0 ≤ y := hx.trans hy.le
    rw [gammaPDF_of_nonneg hy0]
    apply congrArg ENNReal.ofReal
    simp only [Real.one_rpow, one_div]
    rw [show (n : ℝ) + 1 - 1 = n by ring,
      Real.Gamma_nat_eq_factorial, Real.rpow_natCast]
    ring_nf
  rw [hpdf, ← ofReal_integral_eq_lintegral_ofReal hintegrable
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      exact div_nonneg
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (hx.trans hy.le) _))
        (by positivity))]
  rw [integral_pow_mul_exp_neg_Ioi n hx]

/--
Increasing the argument of an integer-shape Gamma survival function by
`δ ≥ 0` loses at most the factor `exp (-δ)`.

This proof uses the finite survival sum directly.  In particular, it avoids
introducing a hazard-rate API merely for the concrete shift in the sparse
upper counterexample.
-/
theorem exp_neg_mul_gammaSurvivalNat_le (n : ℕ) {x δ : ℝ}
    (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    Real.exp (-δ) * gammaSurvivalNat n x ≤
      gammaSurvivalNat n (x + δ) := by
  have hsum :
      (∑ k ∈ Finset.range n, x ^ k / k.factorial) ≤
        ∑ k ∈ Finset.range n, (x + δ) ^ k / k.factorial := by
    apply Finset.sum_le_sum
    intro k _
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hx (le_add_of_nonneg_right hδ) k)
      (by positivity)
  unfold gammaSurvivalNat
  rw [show -(x + δ) = -δ + -x by ring, Real.exp_add]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
      (Real.exp_nonneg _)

/-- The exponential estimate used in the exact `Gamma(128, 1)` comparison. -/
theorem exp_twentyOne_eighth_lt :
    Real.exp (21 / 8 : ℝ) < 2761 / 200 := by
  have hcontains :=
    Exp.posUpper_contains
      (p := 64) (k := 20) (x := (21 / 8 : ℚ))
      (by norm_num) (by norm_num) (by
        change 0 < Dyadic.roundDown 64 (1 - (21 / 8) / 2 ^ 20)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [Dyadic.scale])
  simpa using
    (Interval.lt_of_contains_of_upperLTCheck
      (bound := (2761 / 200 : ℚ)) hcontains (by decide +kernel))

/-- The elementary Taylor lower estimate used for coordinate truncation. -/
theorem twentySeven_fifths_lt_exp_twentySeven_sixteenth :
    (27 / 5 : ℝ) < Real.exp (27 / 16) := by
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg (x := (27 / 16 : ℝ)) (by norm_num) 8)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

/-- Exact cross-multiplication behind the shape-`128` tail estimate. -/
theorem gamma128_rational_comparison :
    (2761 / 200 : ℝ) ^ 128 <
      (2 ^ 129 / 3 : ℝ) *
        ∑ r ∈ Finset.Icc 118 127, (336 : ℝ) ^ r / r.factorial := by
  norm_num [Finset.sum_Icc_succ_top]

/-- The finite shape-`128` survival expression exceeds `3 · 2⁻¹²⁹`. -/
theorem gammaSurvivalNat_128_336_gt :
    gammaSurvivalNat 128 336 >
      (3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
  have hexpPower :
      Real.exp (336 : ℝ) < (2761 / 200 : ℝ) ^ 128 := by
    calc
      Real.exp (336 : ℝ) =
          Real.exp (21 / 8 : ℝ) ^ 128 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ < (2761 / 200 : ℝ) ^ 128 :=
        pow_lt_pow_left₀ exp_twentyOne_eighth_lt
          (Real.exp_nonneg _) (by norm_num)
  have hrational :
      (2761 / 200 : ℝ) ^ 128 <
        (2 ^ 129 / 3 : ℝ) *
          ∑ r ∈ Finset.Icc 118 127,
            (336 : ℝ) ^ r / r.factorial := by
    exact gamma128_rational_comparison
  have htail :
      (∑ r ∈ Finset.Icc 118 127,
          (336 : ℝ) ^ r / r.factorial) ≤
        ∑ r ∈ Finset.range 128,
          (336 : ℝ) ^ r / r.factorial := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      exact Finset.mem_range.mpr (by omega)
    · intro r _ _
      positivity
  have hexpTail :
      Real.exp (336 : ℝ) <
        (2 ^ 129 / 3 : ℝ) *
          ∑ r ∈ Finset.range 128,
            (336 : ℝ) ^ r / r.factorial :=
    hexpPower.trans <| hrational.trans_le <|
      mul_le_mul_of_nonneg_left htail (by positivity)
  unfold gammaSurvivalNat
  rw [Real.exp_neg]
  have hexpPos : 0 < Real.exp (336 : ℝ) := Real.exp_pos _
  rw [gt_iff_lt, inv_mul_eq_div, lt_div_iff₀ hexpPos]
  calc
    (3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128 * Real.exp 336 =
        (3 / 2 ^ 129 : ℝ) * Real.exp 336 := by
      norm_num [inv_pow]
    _ < (3 / 2 ^ 129 : ℝ) *
        ((2 ^ 129 / 3 : ℝ) *
          ∑ r ∈ Finset.range 128,
            (336 : ℝ) ^ r / r.factorial) :=
      mul_lt_mul_of_pos_left hexpTail (by positivity)
    _ = ∑ r ∈ Finset.range 128,
          (336 : ℝ) ^ r / r.factorial := by
      field_simp

/-! ## The threshold-338 security-bit ceiling -/

/-- A compact exponential enclosure at `338 / 128 = 169 / 64`. -/
theorem exp_169_64_lt :
    Real.exp (169 / 64 : ℝ) < 701101 / 50000 := by
  have hcontains :=
    Exp.posUpper_contains
      (p := 64) (k := 20) (x := (169 / 64 : ℚ))
      (by norm_num) (by norm_num) (by
        change 0 < Dyadic.roundDown 64 (1 - (169 / 64) / 2 ^ 20)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [Dyadic.scale])
  simpa using
    (Interval.lt_of_contains_of_upperLTCheck
      (bound := (701101 / 50000 : ℚ)) hcontains (by
        set_option maxRecDepth 100000 in
          decide +kernel))

/-- Exact cross-multiplication behind the 130-bit obstruction at `338`. -/
theorem gamma128_338_rational_comparison :
    (701101 / 50000 : ℝ) ^ 128 <
      (10 * 2 ^ 130 / 17 : ℝ) *
        ∑ r ∈ Finset.Icc 118 127, (338 : ℝ) ^ r / r.factorial := by
  norm_num [Finset.sum_Icc_succ_top]

/-- The shape-`128` Gamma survival probability at `338` exceeds `2⁻¹³⁰`
by the rational factor `17/10`. -/
theorem gammaSurvivalNat_128_338_gt :
    gammaSurvivalNat 128 338 >
      (17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
  have hexpPower :
      Real.exp (338 : ℝ) < (701101 / 50000 : ℝ) ^ 128 := by
    calc
      Real.exp (338 : ℝ) =
          Real.exp (169 / 64 : ℝ) ^ 128 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ < (701101 / 50000 : ℝ) ^ 128 :=
        pow_lt_pow_left₀ exp_169_64_lt
          (Real.exp_nonneg _) (by norm_num)
  have htail :
      (∑ r ∈ Finset.Icc 118 127,
          (338 : ℝ) ^ r / r.factorial) ≤
        ∑ r ∈ Finset.range 128,
          (338 : ℝ) ^ r / r.factorial := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      exact Finset.mem_range.mpr (by omega)
    · intro r _ _
      positivity
  have hexpTail :
      Real.exp (338 : ℝ) <
        (10 * 2 ^ 130 / 17 : ℝ) *
          ∑ r ∈ Finset.range 128,
            (338 : ℝ) ^ r / r.factorial :=
    hexpPower.trans <| gamma128_338_rational_comparison.trans_le <|
      mul_le_mul_of_nonneg_left htail (by positivity)
  unfold gammaSurvivalNat
  rw [Real.exp_neg]
  have hexpPos : 0 < Real.exp (338 : ℝ) := Real.exp_pos _
  rw [gt_iff_lt, inv_mul_eq_div, lt_div_iff₀ hexpPos]
  calc
    (17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130 * Real.exp 338 =
        (17 / (10 * 2 ^ 130) : ℝ) * Real.exp 338 := by
      norm_num [inv_pow]
    _ < (17 / (10 * 2 ^ 130) : ℝ) *
        ((10 * 2 ^ 130 / 17 : ℝ) *
          ∑ r ∈ Finset.range 128,
            (338 : ℝ) ^ r / r.factorial) :=
      mul_lt_mul_of_pos_left hexpTail (by positivity)
    _ = ∑ r ∈ Finset.range 128,
          (338 : ℝ) ^ r / r.factorial := by
      field_simp

/-! ## The 192-row threshold-287 obstruction -/

/-- A compact exponential enclosure at `287 / 96`. -/
theorem exp_287_96_lt :
    Real.exp (287 / 96 : ℝ) < 198789 / 10000 := by
  have hcontains :=
    Exp.posUpper_contains
      (p := 64) (k := 20) (x := (287 / 96 : ℚ))
      (by norm_num) (by norm_num) (by
        change 0 < Dyadic.roundDown 64 (1 - (287 / 96) / 2 ^ 20)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [Dyadic.scale])
  simpa using
    (Interval.lt_of_contains_of_upperLTCheck
      (bound := (198789 / 10000 : ℚ)) hcontains (by
        set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 1000000 in
          decide +kernel))

/-- Exact cross-multiplication behind the 130-bit obstruction at threshold
`287` for 192 half-Gaussian coordinates. -/
theorem gamma96_287_rational_comparison :
    (198789 / 10000 : ℝ) ^ 96 <
      (5 * 2 ^ 130 / 7 : ℝ) *
        ∑ r ∈ Finset.Icc 89 95, (287 : ℝ) ^ r / r.factorial := by
  norm_num [Finset.sum_Icc_succ_top]

/-- The shape-`96` Gamma survival probability at `287` exceeds `2⁻¹³⁰`
by the rational factor `7/5`. -/
theorem gammaSurvivalNat_96_287_gt :
    gammaSurvivalNat 96 287 >
      (7 / 5 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
  have hexpPower :
      Real.exp (287 : ℝ) < (198789 / 10000 : ℝ) ^ 96 := by
    calc
      Real.exp (287 : ℝ) =
          Real.exp (287 / 96 : ℝ) ^ 96 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ < (198789 / 10000 : ℝ) ^ 96 :=
        pow_lt_pow_left₀ exp_287_96_lt
          (Real.exp_nonneg _) (by norm_num)
  have htail :
      (∑ r ∈ Finset.Icc 89 95,
          (287 : ℝ) ^ r / r.factorial) ≤
        ∑ r ∈ Finset.range 96,
          (287 : ℝ) ^ r / r.factorial := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      exact Finset.mem_range.mpr (by omega)
    · intro r _ _
      positivity
  have hexpTail :
      Real.exp (287 : ℝ) <
        (5 * 2 ^ 130 / 7 : ℝ) *
          ∑ r ∈ Finset.range 96,
            (287 : ℝ) ^ r / r.factorial :=
    hexpPower.trans <| gamma96_287_rational_comparison.trans_le <|
      mul_le_mul_of_nonneg_left htail (by positivity)
  unfold gammaSurvivalNat
  rw [Real.exp_neg]
  have hexpPos : 0 < Real.exp (287 : ℝ) := Real.exp_pos _
  rw [gt_iff_lt, inv_mul_eq_div, lt_div_iff₀ hexpPos]
  calc
    (7 / 5 : ℝ) * (2 : ℝ)⁻¹ ^ 130 * Real.exp 287 =
        (7 / (5 * 2 ^ 130) : ℝ) * Real.exp 287 := by
      norm_num [inv_pow]
    _ < (7 / (5 * 2 ^ 130) : ℝ) *
        ((5 * 2 ^ 130 / 7 : ℝ) *
          ∑ r ∈ Finset.range 96,
            (287 : ℝ) ^ r / r.factorial) :=
      mul_lt_mul_of_pos_left hexpTail (by positivity)
    _ = ∑ r ∈ Finset.range 96,
          (287 : ℝ) ^ r / r.factorial := by
      field_simp

end Probability
end CertifiedJL
