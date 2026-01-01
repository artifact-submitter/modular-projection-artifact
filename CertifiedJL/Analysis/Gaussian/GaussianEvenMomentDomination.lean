/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Mass- and variance-parametric Gaussian moment domination

This file packages the algebra used by the positive second Peano replacement.
The measures need not be probability measures: `mass` is a nonnegative upper
bound on their total mass.  The variance parameter is an `NNReal`, so the
centered Gaussian reference is always meaningful.
-/

namespace CertifiedJL

open MeasureTheory ProbabilityTheory

/-- The raw `2 * ell`-th absolute moment of a centered Gaussian with the given
variance. -/
noncomputable def centeredGaussianEvenMoment (variance : NNReal) (ell : ℕ) : ℝ :=
  ∫ x : ℝ, |x| ^ (2 * ell) ∂gaussianReal 0 variance

/-- The variance obtained by multiplying a centered variable by `c`. -/
def scaledVariance (c : ℝ) (variance : NNReal) : NNReal :=
  NNReal.mk (c ^ 2) (sq_nonneg c) * variance

/-- Scaling a centered Gaussian scales its even moments by `|c|^(2*ell)`. -/
theorem centeredGaussianEvenMoment_scaled (c : ℝ) (variance : NNReal) (ell : ℕ) :
    centeredGaussianEvenMoment (scaledVariance c variance) ell =
      |c| ^ (2 * ell) * centeredGaussianEvenMoment variance ell := by
  unfold centeredGaussianEvenMoment scaledVariance
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := variance) c
  simp only [mul_zero] at hmap
  rw [← hmap]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, mul_pow, integral_const_mul]

/-- The independent pushforward law of `w + c * t`, with `w` in the first
coordinate and `t` in the second. -/
noncomputable def independentAffineSumMeasure
    (μ ν : Measure ℝ) (c : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + c * p.2) (μ.prod ν)

private theorem abs_pow_two_mul (x : ℝ) (ell : ℕ) :
    |x| ^ (2 * ell) = x ^ (2 * ell) := by
  rw [pow_mul, pow_mul, sq_abs]

private theorem integral_pow_independentSum_eq_sum
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hν : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) ν)
    (n : ℕ) :
    (∫ z : ℝ, z ^ n ∂independentAffineSumMeasure μ ν 1) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * (∫ w : ℝ, w ^ k ∂μ) *
          ∫ t : ℝ, t ^ (n - k) ∂ν := by
  unfold independentAffineSumMeasure
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [one_mul, add_pow]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_mul_const,
      integral_prod_mul (μ := μ) (ν := ν) (fun w : ℝ => w ^ k)
        (fun t : ℝ => t ^ (n - k))]
    ring
  · intro k hk
    exact ((hμ k).mul_prod (hν (n - k))).mul_const (n.choose k : ℝ)

private theorem integrable_pow_independentSum
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hν : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) ν)
    (n : ℕ) :
    Integrable (fun z : ℝ => z ^ n) (independentAffineSumMeasure μ ν 1) := by
  unfold independentAffineSumMeasure
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  have hfun :
      (fun z : ℝ => z ^ n) ∘ (fun p : ℝ × ℝ => p.1 + 1 * p.2) =
        fun p : ℝ × ℝ => ∑ k ∈ Finset.range (n + 1),
          p.1 ^ k * p.2 ^ (n - k) * (n.choose k : ℝ) := by
    funext p
    simpa only [Function.comp_apply, one_mul] using add_pow p.1 p.2 n
  rw [hfun]
  exact integrable_finsetSum _ fun k _ =>
    ((hμ k).mul_prod (hν (n - k))).mul_const (n.choose k : ℝ)

private theorem independentSum_symmetric
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.map (fun x : ℝ => -x) = μ)
    (hν : ν.map (fun x : ℝ => -x) = ν) :
    (independentAffineSumMeasure μ ν 1).map (fun x : ℝ => -x) =
      independentAffineSumMeasure μ ν 1 := by
  unfold independentAffineSumMeasure
  simp only [one_mul]
  calc
    (Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)).map
        (fun x : ℝ => -x) =
        Measure.map (fun p : ℝ × ℝ => -(p.1 + p.2)) (μ.prod ν) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map (fun p : ℝ × ℝ => -p.1 + -p.2) (μ.prod ν) := by
      congr 1
      funext p
      ring
    _ = Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
        (Measure.map (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x))
          (μ.prod ν)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
        ((μ.map fun x : ℝ => -x).prod (ν.map fun x : ℝ => -x)) := by
      rw [Measure.map_prod_map μ ν (by fun_prop) (by fun_prop)]
    _ = Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) := by
      rw [hμ, hν]

private theorem integral_pow_two_mul_eq_abs
    (μ : Measure ℝ) (ell : ℕ) :
    (∫ x : ℝ, x ^ (2 * ell) ∂μ) = ∫ x : ℝ, |x| ^ (2 * ell) ∂μ := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => (abs_pow_two_mul x ell).symm

/-- A finite symmetric positive measure whose even moments are bounded by
`mass` times those of a centered Gaussian with variance `variance`.

Integrability is recorded for every absolute power, including odd powers,
because product and pushforward consumers need more than the even bounds. -/
structure GaussianEvenMomentDomination
    (μ : Measure ℝ) (mass : ℝ) (variance : NNReal) : Prop where
  mass_nonneg : 0 ≤ mass
  isFiniteMeasure : IsFiniteMeasure μ
  symmetric : μ.map (fun x : ℝ => -x) = μ
  integrable_abs_pow (n : ℕ) : Integrable (fun x : ℝ => |x| ^ n) μ
  integral_even_le (ell : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * ell) ∂μ) ≤
      mass * centeredGaussianEvenMoment variance ell

namespace GaussianEvenMomentDomination

variable {μ : Measure ℝ} {mass : ℝ} {variance : NNReal}

/-- Every raw power is integrable. -/
theorem integrable_pow (h : GaussianEvenMomentDomination μ mass variance) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ := by
  apply (integrable_norm_iff (μ := μ) (f := fun x : ℝ => x ^ n) (by fun_prop)).mp
  simpa only [Real.norm_eq_abs, abs_pow] using h.integrable_abs_pow n

/-- Symmetry cancels every odd raw moment. -/
theorem integral_odd_eq_zero
    (h : GaussianEvenMomentDomination μ mass variance) (ell : ℕ) :
    (∫ x : ℝ, x ^ (2 * ell + 1) ∂μ) = 0 := by
  let : IsFiniteMeasure μ := h.isFiniteMeasure
  have hmap :
      (∫ x : ℝ, x ^ (2 * ell + 1) ∂μ.map (fun x : ℝ => -x)) =
        ∫ x : ℝ, (-x) ^ (2 * ell + 1) ∂μ := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  rw [h.symmetric] at hmap
  have hneg : (∫ x : ℝ, x ^ (2 * ell + 1) ∂μ) =
      -(∫ x : ℝ, x ^ (2 * ell + 1) ∂μ) := by
    calc
      _ = ∫ x : ℝ, (-x) ^ (2 * ell + 1) ∂μ := hmap
      _ = ∫ x : ℝ, -(x ^ (2 * ell + 1)) ∂μ := by
        congr 1
        funext x
        rw [pow_add, pow_mul]
        ring
      _ = _ := integral_neg _
  linarith

/-- The mass parameter bounds the real mass of the measure. -/
theorem measureReal_univ_le
    (h : GaussianEvenMomentDomination μ mass variance) :
    μ.real Set.univ ≤ mass := by
  have h0 := h.integral_even_le 0
  simpa [centeredGaussianEvenMoment] using h0

/-- Moment domination is preserved by deterministic scaling. -/
theorem map_const_mul
    (h : GaussianEvenMomentDomination μ mass variance) (c : ℝ) :
    GaussianEvenMomentDomination
      (μ.map (fun x : ℝ => c * x)) mass (scaledVariance c variance) := by
  let : IsFiniteMeasure μ := h.isFiniteMeasure
  refine ⟨h.mass_nonneg, inferInstance, ?_, ?_, ?_⟩
  · calc
      (μ.map fun x : ℝ => c * x).map (fun x : ℝ => -x) =
          μ.map (fun x : ℝ => -(c * x)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = μ.map (fun x : ℝ => c * (-x)) := by
        congr 1
        funext x
        ring
      _ = (μ.map fun x : ℝ => -x).map (fun x : ℝ => c * x) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = μ.map (fun x : ℝ => c * x) := by rw [h.symmetric]
  · intro n
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    change Integrable (fun x : ℝ => |c * x| ^ n) μ
    simpa only [abs_mul, mul_pow] using
      (h.integrable_abs_pow n).const_mul (|c| ^ n)
  · intro ell
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [abs_mul, mul_pow, integral_const_mul]
    rw [centeredGaussianEvenMoment_scaled]
    calc
      |c| ^ (2 * ell) * (∫ x : ℝ, |x| ^ (2 * ell) ∂μ) ≤
          |c| ^ (2 * ell) *
            (mass * centeredGaussianEvenMoment variance ell) :=
        mul_le_mul_of_nonneg_left (h.integral_even_le ell)
          (pow_nonneg (abs_nonneg c) _)
      _ = mass *
          (|c| ^ (2 * ell) * centeredGaussianEvenMoment variance ell) := by ring

end GaussianEvenMomentDomination

private theorem integrable_abs_pow_gaussianReal (variance : NNReal) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 variance) := by
  have hpow : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 variance) := by
    simpa only [id_eq] using
      (integrable_pow_of_mem_interior_integrableExpSet
        (X := id) (μ := gaussianReal 0 variance) (by simp) n)
  simpa only [Real.norm_eq_abs, abs_pow] using hpow.norm

/-- Every centered Gaussian realizes its own mass-one moment bounds. -/
theorem centeredGaussian_evenMomentDomination (variance : NNReal) :
    GaussianEvenMomentDomination (gaussianReal 0 variance) 1 variance := by
  refine ⟨by positivity, inferInstance, ?_, integrable_abs_pow_gaussianReal variance, ?_⟩
  · simpa using (gaussianReal_map_neg (μ := 0) (v := variance))
  · intro ell
    change centeredGaussianEvenMoment variance ell ≤
      1 * centeredGaussianEvenMoment variance ell
    simp

private theorem centeredGaussianEvenMoment_add
    (variance₁ variance₂ : NNReal) (ell : ℕ) :
    centeredGaussianEvenMoment (variance₁ + variance₂) ell =
      ∑ k ∈ Finset.range (2 * ell + 1),
        ((2 * ell).choose k : ℝ) *
          (∫ w : ℝ, w ^ k ∂gaussianReal 0 variance₁) *
            ∫ t : ℝ, t ^ (2 * ell - k) ∂gaussianReal 0 variance₂ := by
  have hlaw : independentAffineSumMeasure
      (gaussianReal 0 variance₁) (gaussianReal 0 variance₂) 1 =
        gaussianReal 0 (variance₁ + variance₂) := by
    simpa [independentAffineSumMeasure, Measure.conv] using
      (gaussianReal_conv_gaussianReal
        (m₁ := 0) (m₂ := 0) (v₁ := variance₁) (v₂ := variance₂))
  unfold centeredGaussianEvenMoment
  rw [← hlaw, ← integral_pow_two_mul_eq_abs]
  exact integral_pow_independentSum_eq_sum
    (centeredGaussian_evenMomentDomination variance₁).integrable_pow
    (centeredGaussian_evenMomentDomination variance₂).integrable_pow (2 * ell)

private theorem centeredGaussianEvenMoment_le_add
    (variance₁ variance₂ : NNReal) (ell : ℕ) :
    centeredGaussianEvenMoment variance₁ ell ≤
      centeredGaussianEvenMoment (variance₁ + variance₂) ell := by
  rw [centeredGaussianEvenMoment_add]
  have hterm : centeredGaussianEvenMoment variance₁ ell =
      (((2 * ell).choose (2 * ell) : ℝ) *
        (∫ w : ℝ, w ^ (2 * ell) ∂gaussianReal 0 variance₁)) *
          ∫ t : ℝ, t ^ (2 * ell - 2 * ell) ∂gaussianReal 0 variance₂ := by
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero]
    rw [integral_pow_two_mul_eq_abs (gaussianReal 0 variance₁) ell]
    change centeredGaussianEvenMoment variance₁ ell =
      centeredGaussianEvenMoment variance₁ ell *
        ∫ _ : ℝ, (1 : ℝ) ∂gaussianReal 0 variance₂
    simp
  rw [hterm]
  let F : ℕ → ℝ := fun k =>
    (((2 * ell).choose k : ℝ) *
      (∫ w : ℝ, w ^ k ∂gaussianReal 0 variance₁)) *
        ∫ t : ℝ, t ^ (2 * ell - k) ∂gaussianReal 0 variance₂
  change F (2 * ell) ≤ ∑ k ∈ Finset.range (2 * ell + 1), F k
  apply Finset.single_le_sum
  · intro k hk
    by_cases hkeven : Even k
    · rcases hkeven with ⟨a, ha⟩
      have hk_lt : k < 2 * ell + 1 := Finset.mem_range.mp hk
      have hk_le : k ≤ 2 * ell := by omega
      have hk_eq : k = 2 * a := by omega
      have ha_le : a ≤ ell := by omega
      have hrest : 2 * ell - 2 * a = 2 * (ell - a) := by omega
      subst k
      dsimp only [F]
      rw [← two_mul a, hrest,
        integral_pow_two_mul_eq_abs (gaussianReal 0 variance₁) a,
        integral_pow_two_mul_eq_abs (gaussianReal 0 variance₂) (ell - a)]
      positivity
    · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
      rcases hkodd with ⟨a, ha⟩
      have hk_eq : k = 2 * a + 1 := by omega
      subst k
      dsimp only [F]
      rw [
        (centeredGaussian_evenMomentDomination variance₁).integral_odd_eq_zero a]
      norm_num
  · simp

/-- Centered Gaussian even moments are monotone in the variance. -/
theorem centeredGaussianEvenMoment_mono {variance₁ variance₂ : NNReal}
    (hvariance : variance₁ ≤ variance₂) (ell : ℕ) :
    centeredGaussianEvenMoment variance₁ ell ≤
      centeredGaussianEvenMoment variance₂ ell := by
  have hadd : variance₁ + (variance₂ - variance₁) = variance₂ :=
    (add_comm _ _).trans (tsub_add_cancel_of_le hvariance)
  rw [← hadd]
  exact centeredGaussianEvenMoment_le_add variance₁ (variance₂ - variance₁) ell

namespace GaussianEvenMomentDomination

variable {μ ν : Measure ℝ} {mass₁ mass₂ : ℝ} {variance₁ variance₂ : NNReal}

/-- Independent addition preserves Gaussian even-moment domination.  The
product measure in the conclusion is the independence premise. -/
theorem independentSum
    (hμ : GaussianEvenMomentDomination μ mass₁ variance₁)
    (hν : GaussianEvenMomentDomination ν mass₂ variance₂) :
    GaussianEvenMomentDomination
      (independentAffineSumMeasure μ ν 1) (mass₁ * mass₂) (variance₁ + variance₂) := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  let : IsFiniteMeasure ν := hν.isFiniteMeasure
  refine ⟨mul_nonneg hμ.mass_nonneg hν.mass_nonneg,
    Measure.isFiniteMeasure_map (μ.prod ν) (fun p : ℝ × ℝ => p.1 + 1 * p.2),
    independentSum_symmetric hμ.symmetric hν.symmetric, ?_, ?_⟩
  · intro n
    have hpow := integrable_pow_independentSum hμ.integrable_pow hν.integrable_pow n
    simpa only [Real.norm_eq_abs, abs_pow] using hpow.norm
  · intro ell
    rw [← integral_pow_two_mul_eq_abs,
      integral_pow_independentSum_eq_sum hμ.integrable_pow hν.integrable_pow,
      centeredGaussianEvenMoment_add]
    calc
      (∑ k ∈ Finset.range (2 * ell + 1),
          ((2 * ell).choose k : ℝ) * (∫ w : ℝ, w ^ k ∂μ) *
            ∫ t : ℝ, t ^ (2 * ell - k) ∂ν) ≤
          ∑ k ∈ Finset.range (2 * ell + 1),
            (mass₁ * mass₂) *
              (((2 * ell).choose k : ℝ) *
                (∫ w : ℝ, w ^ k ∂gaussianReal 0 variance₁) *
                  ∫ t : ℝ, t ^ (2 * ell - k) ∂gaussianReal 0 variance₂) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk_lt : k < 2 * ell + 1 := Finset.mem_range.mp hk
        by_cases hkeven : Even k
        · rcases hkeven with ⟨a, ha⟩
          have hk_le : k ≤ 2 * ell := by omega
          have hk : k = 2 * a := by omega
          have ha_le : a ≤ ell := by omega
          have hrest : 2 * ell - 2 * a = 2 * (ell - a) := by omega
          rw [hk, hrest,
            integral_pow_two_mul_eq_abs μ a,
            integral_pow_two_mul_eq_abs ν (ell - a),
            integral_pow_two_mul_eq_abs (gaussianReal 0 variance₁) a,
            integral_pow_two_mul_eq_abs (gaussianReal 0 variance₂) (ell - a)]
          have hμ0 : 0 ≤ ∫ w : ℝ, |w| ^ (2 * a) ∂μ :=
            integral_nonneg fun _ => by positivity
          have hν0 : 0 ≤ ∫ t : ℝ, |t| ^ (2 * (ell - a)) ∂ν :=
            integral_nonneg fun _ => by positivity
          have hGμ0 : 0 ≤ centeredGaussianEvenMoment variance₁ a := by
            exact integral_nonneg fun _ => by positivity
          have hGν0 : 0 ≤ centeredGaussianEvenMoment variance₂ (ell - a) := by
            exact integral_nonneg fun _ => by positivity
          have hprod :
              (∫ w : ℝ, |w| ^ (2 * a) ∂μ) *
                  (∫ t : ℝ, |t| ^ (2 * (ell - a)) ∂ν) ≤
                (mass₁ * centeredGaussianEvenMoment variance₁ a) *
                  (mass₂ * centeredGaussianEvenMoment variance₂ (ell - a)) := by
            nlinarith [hμ.integral_even_le a, hν.integral_even_le (ell - a)]
          have hchoose : 0 ≤ ((2 * ell).choose (2 * a) : ℝ) := by positivity
          dsimp only [centeredGaussianEvenMoment] at hprod ⊢
          nlinarith
        · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
          rcases hkodd with ⟨a, ha⟩
          have hk : k = 2 * a + 1 := by omega
          rw [hk, hμ.integral_odd_eq_zero a,
            (centeredGaussian_evenMomentDomination variance₁).integral_odd_eq_zero a]
          norm_num
      _ = (mass₁ * mass₂) *
          ∑ k ∈ Finset.range (2 * ell + 1),
            ((2 * ell).choose k : ℝ) *
              (∫ w : ℝ, w ^ k ∂gaussianReal 0 variance₁) *
                ∫ t : ℝ, t ^ (2 * ell - k) ∂gaussianReal 0 variance₂ := by
        rw [Finset.mul_sum]

/-- Scaling the second coordinate and then adding it to the first preserves
domination, with variance `variance₁ + c² * variance₂`. -/
theorem independentAffineSum
    (hμ : GaussianEvenMomentDomination μ mass₁ variance₁)
    (hν : GaussianEvenMomentDomination ν mass₂ variance₂) (c : ℝ) :
    GaussianEvenMomentDomination
      (independentAffineSumMeasure μ ν c) (mass₁ * mass₂)
        (variance₁ + scaledVariance c variance₂) := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  let : IsFiniteMeasure ν := hν.isFiniteMeasure
  have hscaled := hν.map_const_mul c
  have hadd := hμ.independentSum hscaled
  have hlaw : independentAffineSumMeasure μ ν c =
      independentAffineSumMeasure μ (ν.map fun x : ℝ => c * x) 1 := by
    unfold independentAffineSumMeasure
    simp only [one_mul]
    symm
    have hprod := Measure.map_prod_map
      (f := fun x : ℝ => x) (g := fun x : ℝ => c * x)
      μ ν (by fun_prop) (by fun_prop)
    rw [Measure.map_id'] at hprod
    rw [hprod]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  rw [hlaw]
  exact hadd

/-- Increasing the reference variance weakens the domination claim. -/
theorem variance_mono
    (h : GaussianEvenMomentDomination μ mass₁ variance₁)
    {variance₂ : NNReal} (hvariance : variance₁ ≤ variance₂) :
    GaussianEvenMomentDomination μ mass₁ variance₂ := by
  refine ⟨h.mass_nonneg, h.isFiniteMeasure, h.symmetric,
    h.integrable_abs_pow, ?_⟩
  intro ell
  exact (h.integral_even_le ell).trans
    (mul_le_mul_of_nonneg_left
      (centeredGaussianEvenMoment_mono hvariance ell) h.mass_nonneg)

end GaussianEvenMomentDomination

end CertifiedJL
