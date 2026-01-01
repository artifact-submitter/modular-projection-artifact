import CertifiedJL.Probability.NormalApproximation.Tyurin.ElementaryGaussianMoment

open MeasureTheory Set
namespace CertifiedJL.Probability

/-- The cubic density exponent above its tangent switch is dominated by a
single quadratic chosen at the outer cutoff. -/
theorem tyurin_cubic_exponent_le_cutoff_quadratic {L s T : ℝ}
    (hL : 0 ≤ L) (_hs : 0 ≤ s) (hT : 0 < T) (hsT : s ≤ T)
    (hswitch : 125 / 27 ≤ L * s ^ 3) :
    L * s ^ 3 / 5 + 25 / 54 ≤
      (2 * L * T / 5 + 25 / (27 * T ^ 2)) * s ^ 2 / 2 := by
  have ha : 125 * (T + s) ≤ 250 * T := by linarith
  have hb : 250 * T ≤ 54 * L * s ^ 3 * T := by
    have h := mul_le_mul_of_nonneg_right hswitch hT.le
    nlinarith
  have hc : 54 * L * s ^ 3 * T ≤ 54 * L * T ^ 2 * s ^ 2 := by
    have h := mul_nonneg (by positivity : 0 ≤ 54 * L * T * s ^ 2) (sub_nonneg.mpr hsT)
    nlinarith
  have hd : 0 ≤ (T - s) * (54 * L * T ^ 2 * s ^ 2 - 125 * (T + s)) :=
    mul_nonneg (sub_nonneg.mpr hsT) (by linarith)
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  apply (mul_le_mul_iff_of_pos_right hT2).mp
  field_simp
  nlinarith

theorem tyurinDeltaTwoDensity_le_quadratic {L s T c : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hT : 0 < T) (hsT : s ≤ T)
    (hcap : lyapunovVarianceCap L ≤ c)
    (hcut : 2 * L * T / 5 + 25 / (27 * T ^ 2) ≤ c) :
    tyurinDeltaTwoDensity L s ≤ L * s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2) := by
  unfold tyurinDeltaTwoDensity
  split_ifs with hbranch
  · gcongr
  · have hexp := tyurin_cubic_exponent_le_cutoff_quadratic hL hs hT hsT
      (le_of_not_ge hbranch)
    have hexp' : L * s ^ 3 / 5 + 25 / 54 ≤ c * s ^ 2 / 2 := by
      exact hexp.trans (by gcongr)
    calc
      _ = L * s ^ 2 / 2 * Real.exp (L * s ^ 3 / 5 + 25 / 54) := by
        unfold tyurinRationalEll
        rw [Real.exp_add, Real.exp_neg]
        field_simp
      _ ≤ _ := by gcongr

/-- Both density branches fit one quadratic envelope on the fixed cutoff
interval; the finite trapezoid is used only as an analytic theorem. -/
theorem tyurinDeltaTwo_le_cutoffTrapezoid {L u T c : ℝ}
    (hL : 0 < L) (hu : 0 ≤ u) (hT : 0 < T) (huT : u ≤ T)
    (hc : 0 ≤ c) (hcap : lyapunovVarianceCap L ≤ c)
    (hcut : 2 * L * T / 5 + 25 / (27 * T ^ 2) ≤ c) :
    tyurinDeltaTwo L u ≤
      L * Real.exp (-(u ^ 2) / 2) * sqExpSqTrapezoid 8 c u := by
  have hi := intervalIntegral.integral_mono_on hu
    (intervalIntegrable_tyurinDeltaTwoDensity hL hu)
    ((by fun_prop : Continuous (fun s : ℝ => L * s ^ 2 / 2 *
      Real.exp (c * s ^ 2 / 2))).intervalIntegrable 0 u)
    (fun s hs => tyurinDeltaTwoDensity_le_quadratic hL.le hs.1 hT
      (hs.2.trans huT) hcap hcut)
  have heq : (∫ s : ℝ in 0..u, L * s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)) =
      L * ∫ s : ℝ in 0..u, s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [heq] at hi
  have ht := integral_sq_div_two_mul_exp_sq_le_trapezoid (n := 8) (by norm_num) hu hc
  rw [tyurinDeltaTwo_eq_integral_density hL, abs_of_nonneg hu]
  exact (mul_le_mul_of_nonneg_left
    (hi.trans (mul_le_mul_of_nonneg_left ht hL.le)) (Real.exp_pos _).le).trans_eq (by ring)

/-- The enlarged quadratic coefficient removes the switch condition from
the actual core-integral bound. -/
theorem tyurinCoreIntegral_le_crossingClosed {L b U T c : ℝ}
    (hL : 0 < L) (hLb : L ≤ b) (hT : 0 < T) (hU : 0 < U) (hTU : T ≤ U)
    (hcap : lyapunovVarianceCap b ≤ c)
    (hcut : 2 * b * T / 5 + 25 / (27 * T ^ 2) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ u : ℝ in 0..T, ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
      (b * (513 / 500) / (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) / 2 *
        (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)) := by
  have hb := hL.trans_le hLb
  apply tyurinCoreIntegral_le_closed_of_majorant hL hLb hT hU hTU hc0 hc1
  intro u hu huT
  have hd := (tyurinDeltaTwo_mono hL hLb (t := u)).trans
    (tyurinDeltaTwo_le_cutoffTrapezoid hb hu.le hT huT.le hc0 hcap hcut)
  have hmin := (min_le_right (tyurinDeltaOne L u) (tyurinDeltaTwo L u)).trans hd
  have hchord := mul_le_mul_of_nonneg_left
    (weighted_sqExpSqTrapezoid_eight_le_chord c u hu.le) hb.le
  have hd' : min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      b * (u ^ 3 * (1071 / 16384 * Real.exp (-(u ^ 2) / 2) +
        1681 / 16384 * Real.exp ((c - 1) * u ^ 2 / 2))) := by
    exact hmin.trans (by simpa [mul_assoc] using hchord)
  have hk := norm_scaledPrawitzKernel_le_i29 hU hu.ne'
    (by simpa [abs_of_pos hu] using huT.le.trans hTU)
  simp only [scaledPrawitzI29Envelope, abs_of_pos hu] at hk
  have hm := mul_le_mul hk hd'
    (le_min (tyurinDeltaOne_nonneg hL.le) (tyurinDeltaTwo_nonneg hL)) (by positivity)
  exact hm.trans_eq (by field_simp [hu.ne'])

end CertifiedJL.Probability
