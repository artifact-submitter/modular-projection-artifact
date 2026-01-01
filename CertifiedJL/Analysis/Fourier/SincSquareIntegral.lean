/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Beurling.Majorant
import CertifiedJL.Analysis.Fourier.FourierCDFInversion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The squared-sinc integral

This file proves the normalization of the squared-sinc correction in the
Beurling majorant:

`∫ x : ℝ, sinc (π x) ^ 2 = 1`.

The proof is elementary and uses the Dirichlet integral already established
for Fourier CDF inversion.  On the positive half-line,

`∫₀ᵇ sinc(x)^2 dx = ∫₀²ᵇ sinc(t) dt - b sinc(b)^2`.

The boundary term tends to zero, while the Dirichlet integral tends to
`π / 2`.  Evenness and a change of scale then give the stated normalization.
-/

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

namespace CertifiedJL
namespace Probability

/-- The primitive of `sinc` based at zero. -/
noncomputable def sincIntegral (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.sinc t

theorem hasDerivAt_sincIntegral (x : ℝ) :
    HasDerivAt sincIntegral (Real.sinc x) x := by
  unfold sincIntegral
  exact integral_hasDerivAt_right
    (Real.continuous_sinc.intervalIntegrable 0 x)
    Real.continuous_sinc.aestronglyMeasurable.stronglyMeasurableAtFilter
    Real.continuous_sinc.continuousAt

private theorem mul_sinc_eq_sin (x : ℝ) :
    x * Real.sinc x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

/-- A primitive for squared sinc on the positive half-line. -/
noncomputable def sincSquarePrimitive (x : ℝ) : ℝ :=
  sincIntegral (2 * x) - x * Real.sinc x ^ 2

private theorem hasDerivAt_sincSquarePrimitive_of_pos
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt sincSquarePrimitive (Real.sinc x ^ 2) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have htwo : (2 * x : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hx0
  have hD :
      HasDerivAt (fun y : ℝ => sincIntegral (2 * y))
        (2 * Real.sinc (2 * x)) x := by
    have hraw :=
      (hasDerivAt_sincIntegral (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
    change HasDerivAt (fun y : ℝ => sincIntegral (2 * y))
      (Real.sinc (2 * x) * (2 * 1)) x at hraw
    exact hraw.congr_deriv (by ring)
  have hquot :
      HasDerivAt (fun y : ℝ => Real.sin y ^ 2 / y)
        (((2 * Real.sin x * Real.cos x) * x - Real.sin x ^ 2) / x ^ 2) x := by
    have hraw :=
      ((Real.hasDerivAt_sin x).mul
        (Real.hasDerivAt_sin x)).div (hasDerivAt_id x) hx0
    have hraw' :
        HasDerivAt (Real.sin * Real.sin / id)
          (((2 * Real.sin x * Real.cos x) * x - Real.sin x ^ 2) / x ^ 2) x :=
      hraw.congr_deriv (by
        dsimp
        ring)
    apply hraw'.congr_of_eventuallyEq
    exact Eventually.of_forall fun y => by
      simp only [Pi.div_apply, Pi.mul_apply, id_eq, pow_two]
  have hlocal :
      (fun y : ℝ => y * Real.sinc y ^ 2) =ᶠ[𝓝 x]
        fun y => Real.sin y ^ 2 / y := by
    filter_upwards [eventually_ne_nhds hx0] with y hy
    rw [Real.sinc_of_ne_zero hy]
    field_simp
  have hsecond :
      HasDerivAt (fun y : ℝ => y * Real.sinc y ^ 2)
        (((2 * Real.sin x * Real.cos x) * x - Real.sin x ^ 2) / x ^ 2) x :=
    hquot.congr_of_eventuallyEq hlocal
  have hscalar :
      2 * Real.sinc (2 * x) -
          ((2 * Real.sin x * Real.cos x) * x - Real.sin x ^ 2) / x ^ 2 =
        Real.sinc x ^ 2 := by
    rw [Real.sinc_of_ne_zero hx0, Real.sinc_of_ne_zero htwo,
      Real.sin_two_mul]
    field_simp
    ring
  change HasDerivAt
    (fun y : ℝ => sincIntegral (2 * y) - y * Real.sinc y ^ 2)
    (Real.sinc x ^ 2) x
  exact (hD.sub hsecond).congr_deriv hscalar

private theorem tendsto_sincSquarePrimitive_zero :
    Tendsto sincSquarePrimitive (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hD :
      Tendsto (fun x : ℝ => sincIntegral (2 * x)) (𝓝 0) (𝓝 0) := by
    have hlin :
        Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 (2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have hlin' :
        Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using hlin
    have hcomp :=
      (hasDerivAt_sincIntegral 0).continuousAt.tendsto.comp hlin'
    change Tendsto (fun x : ℝ => sincIntegral (2 * x)) (𝓝 0)
      (𝓝 (sincIntegral 0)) at hcomp
    simpa only [sincIntegral, integral_same] using hcomp
  have hboundary :
      Tendsto (fun x : ℝ => x * Real.sinc x ^ 2) (𝓝 0) (𝓝 0) := by
    have hraw :
        Tendsto (fun x : ℝ => x * Real.sinc x ^ 2) (𝓝 0)
          (𝓝 (0 * Real.sinc 0 ^ 2)) :=
      tendsto_id.mul (Real.continuous_sinc.continuousAt.pow 2).tendsto
    simpa using hraw
  change Tendsto
    (fun x : ℝ => sincIntegral (2 * x) - x * Real.sinc x ^ 2)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [nhdsWithin, sub_zero] using
    (hD.sub hboundary).mono_left
      (inf_le_left : 𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0) ≤ 𝓝 0)

private theorem sincSquarePrimitive_value (b : ℝ) :
    sincSquarePrimitive b =
      (∫ t in (0 : ℝ)..2 * b, Real.sin t / t) -
        b * Real.sinc b ^ 2 := by
  unfold sincSquarePrimitive sincIntegral
  rw [show (∫ t in (0 : ℝ)..2 * b, Real.sinc t) =
      ∫ t in (0 : ℝ)..2 * b, Real.sin t / t by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t ht
    intro _
    exact Real.sinc_of_ne_zero ht]

theorem integral_sinc_sq_zero_to {b : ℝ} (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b, Real.sinc x ^ 2) =
      (∫ t in (0 : ℝ)..2 * b, Real.sin t / t) -
        b * Real.sinc b ^ 2 := by
  rw [← sincSquarePrimitive_value b]
  have hint :
      IntervalIntegrable (fun x : ℝ => Real.sinc x ^ 2) volume 0 b :=
    (Real.continuous_sinc.pow 2).intervalIntegrable 0 b
  have hright :
      Tendsto sincSquarePrimitive (𝓝[<] b)
        (𝓝 (sincSquarePrimitive b)) :=
    (hasDerivAt_sincSquarePrimitive_of_pos hb).continuousAt.tendsto.mono_left
      inf_le_left
  simpa [sincSquarePrimitive] using
    integral_eq_sub_of_hasDerivAt_of_tendsto hb
      (fun x hx => hasDerivAt_sincSquarePrimitive_of_pos hx.1)
      hint tendsto_sincSquarePrimitive_zero hright

private theorem tendsto_mul_sinc_sq_atTop_zero :
    Tendsto (fun b : ℝ => b * Real.sinc b ^ 2) atTop (𝓝 0) := by
  have hbound :
      ∀ᶠ b : ℝ in atTop, |b * Real.sinc b ^ 2| ≤ b⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    have hb0 : b ≠ 0 := hb.ne'
    rw [Real.sinc_of_ne_zero hb0]
    have hvalue :
        b * (Real.sin b / b) ^ 2 = Real.sin b ^ 2 / b := by
      field_simp
    rw [hvalue, abs_div, abs_of_pos hb, abs_sq]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (Real.sin_sq_le_one b) hb.le
  have hupper :
      Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have habs :
      Tendsto (fun b : ℝ => |b * Real.sinc b ^ 2|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      hbound hupper
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

theorem tendsto_integral_sinc_sq_zero_to_atTop :
    Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sinc x ^ 2)
      atTop (𝓝 (Real.pi / 2)) := by
  have htwo :
      Tendsto (fun b : ℝ => 2 * b) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hdirichlet :
      Tendsto
        (fun b : ℝ => ∫ t in (0 : ℝ)..2 * b, Real.sin t / t)
        atTop (𝓝 (Real.pi / 2)) :=
    tendsto_dirichletIntegral_atTop.comp htwo
  have hformula :
      (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sinc x ^ 2) =ᶠ[atTop]
        fun b =>
          (∫ t in (0 : ℝ)..2 * b, Real.sin t / t) -
            b * Real.sinc b ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    exact integral_sinc_sq_zero_to hb
  rw [tendsto_congr' hformula]
  simpa using hdirichlet.sub tendsto_mul_sinc_sq_atTop_zero

theorem integrableOn_sinc_sq_Ioi :
    IntegrableOn (fun x : ℝ => Real.sinc x ^ 2) (Ioi 0) := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto
    (l := atTop) (b := id)
    (f := fun x : ℝ => Real.sinc x ^ 2)
    (μ := volume) (Real.pi / 2) 0
  · intro b
    exact ((Real.continuous_sinc.pow 2).intervalIntegrable 0 b).1
  · exact tendsto_id
  · have hnorm :
        (fun b : ℝ => ∫ x in (0 : ℝ)..b, ‖Real.sinc x ^ 2‖) =
          fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sinc x ^ 2 := by
      funext b
      apply intervalIntegral.integral_congr
      intro x _
      change ‖Real.sinc x ^ 2‖ = Real.sinc x ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := tendsto_integral_sinc_sq_zero_to_atTop
    rw [← hnorm] at h
    simpa only [id_eq] using h

theorem integral_sinc_sq_Ioi :
    ∫ x in Ioi (0 : ℝ), Real.sinc x ^ 2 = Real.pi / 2 := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 integrableOn_sinc_sq_Ioi
      tendsto_id)
    tendsto_integral_sinc_sq_zero_to_atTop

theorem integrable_sinc_sq :
    Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
  have hleft :
      IntegrableOn (fun x : ℝ => Real.sinc x ^ 2) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, Real.sinc_neg, neg_preimage, neg_Iic,
      neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      integrableOn_sinc_sq_Ioi
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    integrableOn_union]
  exact ⟨hleft, integrableOn_sinc_sq_Ioi⟩

private theorem sinc_abs (x : ℝ) :
    Real.sinc |x| = Real.sinc x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, Real.sinc_neg]

theorem integral_sinc_sq :
    ∫ x : ℝ, Real.sinc x ^ 2 = Real.pi := by
  have h := integral_comp_abs (f := fun x : ℝ => Real.sinc x ^ 2)
  simp_rw [sinc_abs] at h
  rw [h, integral_sinc_sq_Ioi]
  ring

theorem integrable_beurlingK :
    Integrable beurlingK := by
  unfold beurlingK
  exact integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero

/-- The squared-sinc correction in the Beurling majorant has mass one. -/
theorem integral_beurlingK :
    ∫ x : ℝ, beurlingK x = 1 := by
  unfold beurlingK
  rw [Measure.integral_comp_mul_left
    (fun y : ℝ => Real.sinc y ^ 2) Real.pi, integral_sinc_sq]
  rw [abs_of_pos (inv_pos.mpr Real.pi_pos)]
  rw [smul_eq_mul]
  field_simp

theorem integrable_scaledBeurlingK_volume {T : ℝ} (hT : T ≠ 0) :
    Integrable (scaledBeurlingK T) := by
  unfold scaledBeurlingK
  exact integrable_beurlingK.comp_mul_left' hT

/-- Scaling the Beurling correction by `T > 0` gives mass `1 / T`. -/
theorem integral_scaledBeurlingK {T : ℝ} (hT : 0 < T) :
    ∫ x : ℝ, scaledBeurlingK T x = 1 / T := by
  unfold scaledBeurlingK
  rw [Measure.integral_comp_mul_left beurlingK T,
    integral_beurlingK, abs_of_pos (inv_pos.mpr hT)]
  ring

end Probability
end CertifiedJL
