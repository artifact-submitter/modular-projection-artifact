import CertifiedJL.Probability.Distributions.Gaussian.StandardGaussian

open MeasureTheory
open scoped ENNReal

namespace CertifiedJL.Probability

/-- The strict Mills inequality for a positive Gaussian tail threshold. -/
theorem integral_Ioi_exp_neg_mul_sq_lt {c b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    (∫ x : ℝ in Set.Ioi b, Real.exp (-c * x ^ 2)) <
      Real.exp (-c * b ^ 2) / (2 * c * b) := by
  let f : ℝ → ℝ := fun x => Real.exp (-c * x ^ 2)
  let g : ℝ → ℝ := fun x => b⁻¹ * (x * Real.exp (-c * x ^ 2))
  have hf : IntegrableOn f (Set.Ioi b) := (integrable_exp_neg_mul_sq hc).integrableOn
  have hg : IntegrableOn g (Set.Ioi b) :=
    ((integrable_mul_exp_neg_mul_sq hc).const_mul b⁻¹).integrableOn
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi b) : 0 < g x - f x := by
    have hone : 1 < b⁻¹ * x := by
      rw [← div_eq_inv_mul, one_lt_div₀ hb]
      exact hx
    dsimp [g, f]
    nlinarith [Real.exp_pos (-c * x ^ 2)]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi b)] (g - f) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpoint x hx).le
  have hsupport : Set.Ioi b ⊆ Function.support (g - f) := by
    intro x hx
    exact ne_of_gt (hpoint x hx)
  have hmeasure : 0 < (volume.restrict (Set.Ioi b)) (Function.support (g - f)) := by
    have hmono := measure_mono (μ := volume.restrict (Set.Ioi b)) hsupport
    have hfull : (volume.restrict (Set.Ioi b)) (Set.Ioi b) = ∞ := by simp
    rw [hfull] at hmono
    exact lt_of_lt_of_le (by simp) hmono
  have hpos := (integral_pos_iff_support_of_nonneg_ae hnonneg (hg.sub hf)).2 hmeasure
  simp only [Pi.sub_apply] at hpos
  rw [integral_sub hg hf] at hpos
  have hlt : (∫ x in Set.Ioi b, f x) < ∫ x in Set.Ioi b, g x := by linarith
  calc
    (∫ x in Set.Ioi b, Real.exp (-c * x ^ 2)) <
        ∫ x in Set.Ioi b, b⁻¹ * (x * Real.exp (-c * x ^ 2)) := hlt
    _ = Real.exp (-c * b ^ 2) / (2 * c * b) := by
      rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hc hb.le]
      field_simp

/-- The paper's strict standard-Gaussian Mills bound. -/
theorem standardGaussianTail_lt_mills {z : ℝ} (hz : 0 < z) :
    standardGaussianTail z <
      Real.exp (-z ^ 2 / 2) / (Real.sqrt (2 * Real.pi) * z) := by
  have h := integral_Ioi_exp_neg_mul_sq_lt (c := (1 / 2 : ℝ)) (by norm_num) hz
  have heq : (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y ^ 2)) =
      (fun y : ℝ => Real.exp (-y ^ 2 / 2)) := by
    funext y
    congr 1
    ring
  rw [heq] at h
  rw [show -(1 / 2 : ℝ) * z ^ 2 = -z ^ 2 / 2 by ring] at h
  unfold standardGaussianTail standardGaussianDensity
  rw [integral_const_mul]
  have hs : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hmul := mul_lt_mul_of_pos_left h hs
  calc
    _ < (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-z ^ 2 / 2) / (2 * (1 / 2) * z)) := hmul
    _ = Real.exp (-z ^ 2 / 2) / (Real.sqrt (2 * Real.pi) * z) := by ring

end CertifiedJL.Probability
