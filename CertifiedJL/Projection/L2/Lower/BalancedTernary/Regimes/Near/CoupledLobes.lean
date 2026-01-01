/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Coupled

/-!
# Coupled retained-coordinate bounds on every cosine lobe

The coarse near-band endpoint must retain the distinguished cosine factor on
nonzero lobes.  Completing the Gaussian square leaves a shifted Gaussian;
its cosine-square expectation is bounded by the centered value, uniformly in
the shift.  This yields one common retained factor multiplying the complete
integer-image sum.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL

/-- Cosine transform of a Gaussian with arbitrary mean and positive or zero
variance. -/
theorem gaussian_cosine_charFun_mean (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    ∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal m v) =
      Real.exp (-(v : ℝ) * t ^ 2 / 2) * Real.cos (t * m) := by
  have h_int :
      Integrable (fun x : ℝ => Complex.exp ((t * x) * Complex.I))
        (gaussianReal m v) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · fun_prop
    · filter_upwards with x
      simpa only [Complex.ofReal_mul] using
        (Complex.norm_exp_ofReal_mul_I (t * x)).le
  have h_re := integral_re h_int
  calc
    ∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal m v) =
        ∫ x : ℝ, (Complex.exp ((t * x) * Complex.I)).re
          ∂(gaussianReal m v) := by
      congr 1
      funext x
      simpa only [Complex.ofReal_mul] using
        (Complex.exp_ofReal_mul_I_re (t * x)).symm
    _ = (MeasureTheory.charFun (gaussianReal m v) t).re := by
      rw [MeasureTheory.charFun_apply_real]
      rw [← RCLike.re_eq_complex_re]
      exact h_re
    _ = Real.exp (-(v : ℝ) * t ^ 2 / 2) * Real.cos (t * m) := by
      rw [ProbabilityTheory.charFun_gaussianReal]
      have hexp :
          Complex.exp
              ((t : ℂ) * (m : ℂ) * Complex.I -
                ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) =
            (Real.exp (-(v : ℝ) * t ^ 2 / 2) : ℝ) *
              Complex.exp ((t * m : ℝ) * Complex.I) := by
        calc
          Complex.exp
              ((t : ℂ) * (m : ℂ) * Complex.I -
                ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) =
            Complex.exp
              (((-(v : ℝ) * t ^ 2 / 2 : ℝ) : ℂ) +
                ((t * m : ℝ) : ℂ) * Complex.I) := by
              congr 1
              push_cast
              ring
          _ = Complex.exp (((-(v : ℝ) * t ^ 2 / 2 : ℝ) : ℂ)) *
                Complex.exp (((t * m : ℝ) : ℂ) * Complex.I) := by
              rw [Complex.exp_add]
          _ = (Real.exp (-(v : ℝ) * t ^ 2 / 2) : ℝ) *
                Complex.exp ((t * m : ℝ) * Complex.I) := by
              rw [Complex.ofReal_exp]
      rw [hexp, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [Complex.exp_ofReal_mul_I_re]

/-- A shifted Gaussian's cosine-square expectation never exceeds the
centered one. -/
theorem gaussian_cos_sq_integral_le_centered (m : ℝ) (v : ℝ≥0) (A : ℝ) :
    (∫ x : ℝ, Real.cos (A * x) ^ 2 ∂(gaussianReal m v)) ≤
      (1 + Real.exp (-2 * (v : ℝ) * A ^ 2)) / 2 := by
  have hcos : Integrable (fun x : ℝ => Real.cos ((2 * A) * x))
      (gaussianReal m v) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with x
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one ((2 * A) * x)
  calc
    (∫ x : ℝ, Real.cos (A * x) ^ 2 ∂(gaussianReal m v)) =
        ∫ x : ℝ, (1 + Real.cos ((2 * A) * x)) / 2
          ∂(gaussianReal m v) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Real.cos_sq]
      congr 2
      ring
    _ = (1 + ∫ x : ℝ, Real.cos ((2 * A) * x)
          ∂(gaussianReal m v)) / 2 := by
      rw [integral_div]
      rw [integral_add (integrable_const 1) hcos]
      simp
    _ = (1 + Real.exp (-2 * (v : ℝ) * A ^ 2) *
          Real.cos ((2 * A) * m)) / 2 := by
      rw [gaussian_cosine_charFun_mean]
      congr 2
      ring
    _ ≤ (1 + Real.exp (-2 * (v : ℝ) * A ^ 2)) / 2 := by
      have hcosle := Real.cos_le_one ((2 * A) * m)
      have hexp0 := Real.exp_nonneg (-2 * (v : ℝ) * A ^ 2)
      have hmul := mul_le_mul_of_nonneg_left hcosle hexp0
      linarith

/-- Completing the Gaussian square on one residual cosine lobe retains the
distinguished cosine-square damping.  The remaining shifted cosine phase can
only decrease its expectation. -/
theorem gaussian_shifted_lobe_mul_cos_sq_integral_le
    {u p B : ℝ} (hu : 0 < u) (hp : 0 < p) (hBsq : B ^ 2 = u / p)
    (A : ℝ) (k : ℤ) :
    (∫ x : ℝ,
        Real.exp (-p * (B * x - (k : ℝ) * Real.pi) ^ 2 / 2) *
          Real.cos (A * x) ^ 2 ∂(gaussianReal 0 1)) ≤
      Real.exp (-(p * (k : ℝ) ^ 2 * Real.pi ^ 2) /
          (2 * (1 + u))) *
        ((1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u))) := by
  let D : ℝ := 1 + u
  have hD : 0 < D := by dsimp [D]; linarith
  let v : ℝ≥0 := ⟨D⁻¹, inv_nonneg.mpr hD.le⟩
  have hv : v ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    change D⁻¹ ≠ 0
    exact inv_ne_zero hD.ne'
  let m : ℝ := p * B * (k : ℝ) * Real.pi / D
  let weight : ℝ :=
    Real.exp (-(p * (k : ℝ) ^ 2 * Real.pi ^ 2) / (2 * D)) /
      Real.sqrt D
  have hweight : 0 ≤ weight := by dsimp [weight]; positivity
  have hdensity (x : ℝ) :
      ProbabilityTheory.gaussianPDFReal 0 1 x *
          (Real.exp (-p * (B * x - (k : ℝ) * Real.pi) ^ 2 / 2) *
            Real.cos (A * x) ^ 2) =
        weight *
          (ProbabilityTheory.gaussianPDFReal m v x *
            Real.cos (A * x) ^ 2) := by
    unfold ProbabilityTheory.gaussianPDFReal
    norm_num only [NNReal.coe_one, mul_one, sub_zero]
    have hsqrtD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
    have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hsqrtDiv :
        Real.sqrt (2 * Real.pi / D) =
          Real.sqrt (2 * Real.pi) / Real.sqrt D := by
      exact Real.sqrt_div (by positivity) D
    have hvariance : (v : ℝ) = 1 / D := by
      change D⁻¹ = 1 / D
      rw [one_div]
    rw [hvariance]
    rw [show 2 * Real.pi * (1 / D) = 2 * Real.pi / D by ring,
      hsqrtDiv]
    have hexponent :
        -(x ^ 2) / 2 +
            (-p * (B * x - (k : ℝ) * Real.pi) ^ 2 / 2) =
          -(p * (k : ℝ) ^ 2 * Real.pi ^ 2) / (2 * D) -
            (x - m) ^ 2 / (2 * (1 / D)) := by
      have hpu : p * B ^ 2 = u := by
        rw [hBsq]
        field_simp [hp.ne']
      dsimp [D, m]
      field_simp [show 1 + u ≠ 0 by linarith]
      linear_combination
        (p * (((k : ℝ) * Real.pi) ^ 2) - (1 + u) * x ^ 2) * hpu
    calc
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
          (Real.exp (-p * (B * x - (k : ℝ) * Real.pi) ^ 2 / 2) *
            Real.cos (A * x) ^ 2) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(x ^ 2) / 2 +
            (-p * (B * x - (k : ℝ) * Real.pi) ^ 2 / 2)) *
              Real.cos (A * x) ^ 2 := by rw [Real.exp_add]; ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (-(p * (k : ℝ) ^ 2 * Real.pi ^ 2) / (2 * D)) *
            Real.exp (-(x - m) ^ 2 / (2 * (1 / D)))) *
              Real.cos (A * x) ^ 2 := by
        rw [hexponent]
        rw [show
            -(p * (k : ℝ) ^ 2 * Real.pi ^ 2) / (2 * D) -
                (x - m) ^ 2 / (2 * (1 / D)) =
              -(p * (k : ℝ) ^ 2 * Real.pi ^ 2) / (2 * D) +
                (-(x - m) ^ 2 / (2 * (1 / D))) by ring,
          Real.exp_add]
      _ = weight *
          ((Real.sqrt (2 * Real.pi) / Real.sqrt D)⁻¹ *
            Real.exp (-(x - m) ^ 2 / (2 * (1 / D))) *
              Real.cos (A * x) ^ 2) := by
        dsimp [weight]
        field_simp [hsqrtD.ne', hsqrtTwoPi.ne']
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  calc
    (∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 x *
        (Real.exp (-p * (B * x - (k : ℝ) * Real.pi) ^ 2 / 2) *
          Real.cos (A * x) ^ 2)) =
      ∫ x : ℝ, weight *
        (ProbabilityTheory.gaussianPDFReal m v x *
          Real.cos (A * x) ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hdensity x
    _ = weight * ∫ x : ℝ,
        ProbabilityTheory.gaussianPDFReal m v x *
          Real.cos (A * x) ^ 2 := by rw [integral_const_mul]
    _ = weight * ∫ x : ℝ, Real.cos (A * x) ^ 2
        ∂(gaussianReal m v) := by
      rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
      simp only [smul_eq_mul]
    _ ≤ weight *
        ((1 + Real.exp (-2 * (v : ℝ) * A ^ 2)) / 2) := by
      exact mul_le_mul_of_nonneg_left
        (gaussian_cos_sq_integral_le_centered m v A) hweight
    _ = Real.exp (-(p * (k : ℝ) ^ 2 * Real.pi ^ 2) /
          (2 * (1 + u))) *
        ((1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u))) := by
      have hvD : (v : ℝ) = 1 / D := by
        change D⁻¹ = 1 / D
        rw [one_div]
      rw [hvD]
      have hden : 1 + u ≠ 0 := by linarith
      rw [show -2 * (1 / D) * A ^ 2 = -2 * A ^ 2 / D by
        field_simp [hD.ne']]
      dsimp [weight, D]
      ring

/-- Periodizing every residual cosine lobe while retaining the distinguished
cosine factor gives a *multiplicative* image allowance.  This is sharper than
discarding the retained factor outside the central lobe. -/
theorem retainedGaussianRpowMoment_le_coupled_geometricTail
    {A u y : ℝ} (hu : 0 < u) (hy : 0 < y) :
    (∫ G : ℝ, Real.cos (A * G) ^ 2 *
        |Real.cos (Real.sqrt (u / (2 / y)) * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) ≤
      (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) *
        (1 + 2 * Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) /
          (1 - Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) ^ 3)) := by
  let p : ℝ := 2 / y
  let B : ℝ := Real.sqrt (u / p)
  let C : ℤ → Set ℝ := fun k => {G : ℝ | B * G ∈ scalarLobe k}
  let f : ℝ → ℝ := fun G =>
    Real.cos (A * G) ^ 2 * |Real.cos (B * G)| ^ p
  let base : ℝ :=
    (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
      (2 * Real.sqrt (1 + u))
  let c : ℝ := Real.pi ^ 2 / (y * (1 + u))
  have hp : 0 < p := by dsimp [p]; positivity
  have hu_div_p : 0 < u / p := div_pos hu hp
  have hB : 0 < B := by dsimp [B]; positivity
  have hBsq : B ^ 2 = u / p := by
    dsimp [B]
    exact Real.sq_sqrt hu_div_p.le
  have hc : 0 < c := by dsimp [c]; positivity
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hC (k : ℤ) : MeasurableSet (C k) :=
    (measurableSet_scalarLobe k).preimage (by fun_prop)
  have hdis : Pairwise (fun k l => Disjoint (C k) (C l)) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro G hGk hGl
    exact Set.disjoint_left.mp (scalarLobe_pairwise_disjoint hkl) hGk hGl
  have hcover : (⋃ k : ℤ, C k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro G
    have hmem : B * G ∈ ⋃ k : ℤ, scalarLobe k := by
      rw [scalarLobe_cover]
      trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  have hf : Integrable f (gaussianReal 0 1) := by
    refine Integrable.of_bound (by dsimp [f]; fun_prop) 1 ?_
    filter_upwards [] with G
    dsimp [f]
    rw [abs_mul, abs_sq,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact mul_le_one₀
      ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))
      (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one _) hp.le)
  have hg (k : ℤ) : Integrable (fun G : ℝ =>
      Real.exp (-p * (B * G - (k : ℝ) * Real.pi) ^ 2 / 2) *
        Real.cos (A * G) ^ 2) (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with G
    rw [Real.norm_eq_abs, abs_mul, abs_sq,
      abs_of_nonneg (Real.exp_nonneg _)]
    have hexp :
        Real.exp (-p * (B * G - (k : ℝ) * Real.pi) ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hmul : 0 ≤ p * (B * G - (k : ℝ) * Real.pi) ^ 2 :=
        mul_nonneg hp.le (sq_nonneg _)
      linarith
    exact mul_le_one₀ hexp (sq_nonneg _)
      ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))
  have hpoint (k : ℤ) (G : ℝ) (hG : G ∈ C k) :
      f G ≤
        Real.exp (-p * (B * G - (k : ℝ) * Real.pi) ^ 2 / 2) *
          Real.cos (A * G) ^ 2 := by
    have hcos := scalarLobe_cosineEnvelope hG
    have hpow := Real.rpow_le_rpow (abs_nonneg _) hcos hp.le
    have hpow_exp :
        (Real.exp (-((B * G - (k : ℝ) * Real.pi) ^ 2) / 2)) ^ p =
          Real.exp (-p * (B * G - (k : ℝ) * Real.pi) ^ 2 / 2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [hpow_exp] at hpow
    dsimp [f]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hpow (sq_nonneg (Real.cos (A * G))))
  have hterm (k : ℤ) :
      (∫ G in C k, f G ∂(gaussianReal 0 1)) ≤
        Real.exp (-c * (k : ℝ) ^ 2) * base := by
    calc
      (∫ G in C k, f G ∂(gaussianReal 0 1)) ≤
          ∫ G in C k,
            Real.exp (-p * (B * G - (k : ℝ) * Real.pi) ^ 2 / 2) *
              Real.cos (A * G) ^ 2 ∂(gaussianReal 0 1) := by
        exact setIntegral_mono_on hf.integrableOn (hg k).integrableOn
          (hC k) (hpoint k)
      _ ≤ ∫ G : ℝ,
            Real.exp (-p * (B * G - (k : ℝ) * Real.pi) ^ 2 / 2) *
              Real.cos (A * G) ^ 2 ∂(gaussianReal 0 1) := by
        apply setIntegral_le_integral (hg k)
        filter_upwards [] with G
        exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
      _ ≤ Real.exp (-(p * (k : ℝ) ^ 2 * Real.pi ^ 2) /
            (2 * (1 + u))) * base := by
        simpa only [base] using
          gaussian_shifted_lobe_mul_cos_sq_integral_le hu hp hBsq A k
      _ = Real.exp (-c * (k : ℝ) ^ 2) * base := by
        congr 2
        dsimp [c, p]
        field_simp [hy.ne', (show 1 + u ≠ 0 by linarith)]
  have hsumLeft : Summable
      (fun k : ℤ => ∫ G in C k, f G ∂(gaussianReal 0 1)) := by
    exact (hasSum_integral_iUnion (f := f) (fun k : ℤ => hC k) hdis
      (hf.integrableOn.mono_set (by rw [hcover]))).summable
  have hsumRight : Summable
      (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2) * base) :=
    (summable_real_integer_exp_neg_sq hc).mul_right base
  have hdecomp :
      (∫ G : ℝ, f G ∂(gaussianReal 0 1)) =
        ∑' k : ℤ, ∫ G in C k, f G ∂(gaussianReal 0 1) := by
    have h := integral_iUnion (f := f) (fun k : ℤ => hC k) hdis
      (hf.integrableOn.mono_set (by rw [hcover]))
    rw [hcover] at h
    simpa using h
  have hsumBound :
      (∑' k : ℤ, ∫ G in C k, f G ∂(gaussianReal 0 1)) ≤
        ∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2) * base :=
    hsumLeft.tsum_le_tsum hterm hsumRight
  have htail := scalarLobe_real_integer_exp_geometricTail hc
  rw [show Real.sqrt (u / (2 / y)) = B by rfl,
    show (2 / y : ℝ) = p by rfl]
  change (∫ G : ℝ, f G ∂(gaussianReal 0 1)) ≤ _
  rw [hdecomp]
  calc
    (∑' k : ℤ, ∫ G in C k, f G ∂(gaussianReal 0 1)) ≤
        ∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2) * base := hsumBound
    _ = (∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2)) * base := by
      rw [tsum_mul_right]
    _ ≤ (1 + 2 * Real.exp (-c) / (1 - Real.exp (-c) ^ 3)) *
          base := mul_le_mul_of_nonneg_right htail hbase0
    _ = base *
        (1 + 2 * Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) /
          (1 - Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) ^ 3)) := by
      dsimp [c]
      ring
    _ = _ := by rfl

end CertifiedJL
