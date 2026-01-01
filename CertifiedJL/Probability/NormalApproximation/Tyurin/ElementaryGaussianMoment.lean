import CertifiedJL.Probability.NormalApproximation.Tyurin.ElementaryCore
import Mathlib.MeasureTheory.Integral.Gamma
import CertifiedJL.Probability.NormalApproximation.Tyurin.DStarCertificate
import CertifiedJL.Probability.NormalApproximation.Tyurin.DeltaMonotonicity

open MeasureTheory Set
namespace CertifiedJL.Probability

theorem integral_quadraticGaussian_Ioi (d : ℝ) (hd : 0 < d) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-d * t ^ 2 / 2)) =
      (d / 2) ^ (-(3 : ℝ) / 2) * Real.sqrt Real.pi / 4 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (2 : ℝ)) (b := d / 2)
    (by norm_num) (by norm_num) (by positivity)
  have hg : Real.Gamma ((3 : ℝ) / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  norm_num only [Real.rpow_ofNat, show ((2 : ℝ) + 1) = 3 by norm_num] at h
  rw [hg] at h
  convert h using 1
  · congr 1; funext t; congr 2; ring
  · ring

/-- Inflating the exact `d^(-3/2)` moment to `d^(-2)` removes cube roots
from the final closed certificate. -/
theorem integral_quadraticGaussian_Ioi_le_square
    (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-d * t ^ 2 / 2)) ≤
      (1 / d ^ 2) * (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
  rw [integral_quadraticGaussian_Ioi d hd]
  have hb := integral_quadraticGaussian_Ioi 1 (by norm_num)
  simp only [neg_mul, one_mul] at hb
  rw [hb, show d / 2 = d * (2 : ℝ)⁻¹ by ring,
    Real.mul_rpow hd.le (by positivity)]
  have hpow := Real.rpow_le_rpow_of_exponent_ge hd hd1
    (show (-2 : ℝ) ≤ -(3 : ℝ) / 2 by norm_num)
  have hneg : d ^ (-2 : ℝ) = 1 / d ^ 2 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hd.le,
      Real.rpow_two, one_div]
  rw [hneg] at hpow
  calc
    _ ≤ (1 / d ^ 2) * ((2 : ℝ)⁻¹ ^ (-(3 : ℝ) / 2)) * Real.sqrt Real.pi / 4 := by
      gcongr
    _ = _ := by ring

theorem integral_standardGaussian_second_Ioi :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-t ^ 2 / 2)) =
      Real.sqrt (2 * Real.pi) / 2 := by
  have h := integral_quadraticGaussian_Ioi 1 (by norm_num)
  simp only [neg_mul, one_mul] at h
  rw [h]
  rw [show (-(3 : ℝ) / 2) = -(1 + 1 / 2) by norm_num,
    Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), Real.sqrt_one,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ; ring

theorem integrableOn_quadraticGaussian_Ioi (d : ℝ) (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-d * t ^ 2 / 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (2 : ℝ)) (p := (2 : ℝ)) (b := d / 2)
    (by norm_num) (by norm_num) (by positivity)
  simp only [Real.rpow_ofNat] at h
  convert h using 1
  ext t
  congr 2
  ring

/-- Closed upper bound for the entire nonnegative chord integrand. This is
the reusable analytic step that removes the outer core-rectangle mesh. -/
theorem integral_chordMajorant_Ioi_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ t : ℝ in Ioi 0, t ^ 2 *
      (1071 / 16384 * Real.exp (-(t ^ 2) / 2) +
        1681 / 16384 * Real.exp ((c - 1) * t ^ 2 / 2))) ≤
      Real.sqrt (2 * Real.pi) / 2 *
        (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2) := by
  have hd : 0 < 1 - c := by linarith
  have hd1 : 1 - c ≤ 1 := by linarith
  have hi0 := integrableOn_quadraticGaussian_Ioi 1 (by norm_num)
  simp only [neg_mul, one_mul] at hi0
  have hi1 := integrableOn_quadraticGaussian_Ioi (1 - c) hd
  have hfn : (fun t : ℝ => t ^ 2 *
      (1071 / 16384 * Real.exp (-(t ^ 2) / 2) +
        1681 / 16384 * Real.exp ((c - 1) * t ^ 2 / 2))) =
      (fun t : ℝ => (1071 / 16384) * (t ^ 2 * Real.exp (-(t ^ 2) / 2)) +
        (1681 / 16384) * (t ^ 2 * Real.exp (-(1 - c) * t ^ 2 / 2))) := by
    funext t
    rw [show (c - 1) * t ^ 2 / 2 = -(1 - c) * t ^ 2 / 2 by ring]
    ring
  rw [hfn, integral_add (hi0.const_mul _) (hi1.const_mul _),
    integral_const_mul, integral_const_mul, integral_standardGaussian_second_Ioi]
  have hb := integral_quadraticGaussian_Ioi_le_square (1 - c) hd hd1
  rw [integral_standardGaussian_second_Ioi] at hb
  calc
    _ ≤ 1071 / 16384 * (Real.sqrt (2 * Real.pi) / 2) +
      1681 / 16384 * ((1 / (1 - c) ^ 2) * (Real.sqrt (2 * Real.pi) / 2)) := by
      gcongr
    _ = _ := by ring

/-- Before the Tyurin switch, the actual discrepancy/kernel integrand has
a smooth Gaussian majorant, including its removable singularity at zero. -/
theorem tyurinCore_le_chordMajorant {L b U u c : ℝ}
    (hL : 0 < L) (hLb : L ≤ b) (hU : 0 < U) (hu : 0 < u) (huU : u ≤ U)
    (hswitch : u * lyapunovThirdRoot b ≤ 5 / 3)
    (hcap : lyapunovVarianceCap b ≤ c) :
    ‖scaledPrawitzKernel U u‖ * min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      (b * (513 / 500) / (2 * Real.pi)) * (u ^ 2 *
        (1071 / 16384 * Real.exp (-(u ^ 2) / 2) +
          1681 / 16384 * Real.exp ((c - 1) * u ^ 2 / 2))) := by
  have hb : 0 < b := hL.trans_le hLb
  have hd := tyurinDeltaTwo_le_endpointTrapezoid (n := 8) (by norm_num) hL hLb
    (t := u)
  simp only [tyurinDeltaTwoTrapezoidUpper, abs_of_pos hu, if_pos hswitch] at hd
  have hc := weighted_sqExpSqTrapezoid_eight_le_chord (lyapunovVarianceCap b) u hu.le
  have hd' := (min_le_right (tyurinDeltaOne L u) (tyurinDeltaTwo L u)).trans hd
  have hdc : min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      b * (u ^ 3 * (1071 / 16384 * Real.exp (-(u ^ 2) / 2) +
        1681 / 16384 * Real.exp ((c - 1) * u ^ 2 / 2))) := by
    calc
      _ ≤ b * (Real.exp (-(u ^ 2) / 2) *
        sqExpSqTrapezoid 8 (lyapunovVarianceCap b) u) := by simpa [mul_assoc] using hd'
      _ ≤ b * (u ^ 3 * (1071 / 16384 * Real.exp (-(u ^ 2) / 2) +
        1681 / 16384 * Real.exp ((lyapunovVarianceCap b - 1) * u ^ 2 / 2))) := by
          exact mul_le_mul_of_nonneg_left hc hb.le
      _ ≤ _ := by gcongr
  have hk := norm_scaledPrawitzKernel_le_i29 hU hu.ne' (by simpa [abs_of_pos hu] using huU)
  simp only [scaledPrawitzI29Envelope, abs_of_pos hu] at hk
  have hm := mul_le_mul hk hdc
    (le_min (tyurinDeltaOne_nonneg hL.le) (tyurinDeltaTwo_nonneg hL)) (by positivity)
  exact hm.trans_eq (by field_simp [hu.ne'])

/-- Integrate any proved Gaussian chord majorant without a core mesh. -/
theorem tyurinCoreIntegral_le_closed_of_majorant {L b U T c : ℝ}
    (hL : 0 < L) (hLb : L ≤ b) (hT : 0 < T) (hU : 0 < U) (hTU : T ≤ U)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hmajorant : ∀ u, 0 < u → u < T →
      ‖scaledPrawitzKernel U u‖ * min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
        (b * (513 / 500) / (2 * Real.pi)) * (u ^ 2 *
          (1071 / 16384 * Real.exp (-(u ^ 2) / 2) +
            1681 / 16384 * Real.exp ((c - 1) * u ^ 2 / 2)))) :
    (∫ u : ℝ in 0..T, ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
      (b * (513 / 500) / (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) / 2 *
        (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)) := by
  let K := b * (513 / 500) / (2 * Real.pi)
  let g : ℝ → ℝ := fun u => u ^ 2 *
    (1071 / 16384 * Real.exp (-(u ^ 2) / 2) +
      1681 / 16384 * Real.exp ((c - 1) * u ^ 2 / 2))
  have hb : 0 < b := hL.trans_le hLb
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hgi : IntegrableOn g (Ioi 0) := by
    have h0 := integrableOn_quadraticGaussian_Ioi 1 (by norm_num)
    have h1 := integrableOn_quadraticGaussian_Ioi (1 - c) (by linarith)
    have heq : g = (fun u => (1071 / 16384) * (u ^ 2 * Real.exp (-1 * u ^ 2 / 2))) +
        (fun u => (1681 / 16384) * (u ^ 2 * Real.exp (-(1 - c) * u ^ 2 / 2))) := by
      funext u
      dsimp [g]
      rw [show (c - 1) * u ^ 2 / 2 = -(1 - c) * u ^ 2 / 2 by ring]
      simp only [neg_mul, one_mul]
      ring
    rw [heq]
    exact (h0.const_mul (1071 / 16384)).add (h1.const_mul (1681 / 16384))
  have hg0 (u : ℝ) : 0 ≤ g u := by dsimp [g]; positivity
  have hf := intervalIntegrable_tyurinCoreIntegrand
    (n := 8) (by norm_num) hL hT hU hTU
  have hpoint := intervalIntegral.integral_mono_on_of_le_Ioo hT.le hf
    ((hgc.const_mul K).intervalIntegrable 0 T) (fun u hu => hmajorant u hu.1 hu.2)
  have hset : (∫ u : ℝ in 0..T, g u) ≤ ∫ u : ℝ in Ioi 0, g u := by
    rw [intervalIntegral.integral_of_le hT.le]
    exact setIntegral_mono_set hgi (Filter.Eventually.of_forall hg0)
      (Filter.Eventually.of_forall (fun _ hu => hu.1))
  calc
    _ ≤ ∫ u : ℝ in 0..T, K * g u := hpoint
    _ = K * ∫ u : ℝ in 0..T, g u := intervalIntegral.integral_const_mul K g
    _ ≤ K * ∫ u : ℝ in Ioi 0, g u := mul_le_mul_of_nonneg_left hset hK
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_chordMajorant_Ioi_le c hc0 hc1) hK

/-- A closed bound for the actual core integral on any cell wholly before
the Tyurin switch. No core quadrature hypotheses occur in this theorem. -/
theorem tyurinCoreIntegral_le_closed {L b U T c : ℝ}
    (hL : 0 < L) (hLb : L ≤ b) (hT : 0 < T) (hU : 0 < U) (hTU : T ≤ U)
    (hswitch : T * lyapunovThirdRoot b ≤ 5 / 3)
    (hcap : lyapunovVarianceCap b ≤ c) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ u : ℝ in 0..T, ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
      (b * (513 / 500) / (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) / 2 *
        (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)) := by
  apply tyurinCoreIntegral_le_closed_of_majorant hL hLb hT hU hTU hc0 hc1
  intro u hu huT
  apply tyurinCore_le_chordMajorant hL hLb hU hu (huT.le.trans hTU) _ hcap
  exact (mul_le_mul_of_nonneg_right huT.le
    (lyapunovThirdRoot_nonneg (hL.trans_le hLb).le)).trans hswitch

end CertifiedJL.Probability
