/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.RademacherEntropyProfile
import CertifiedJL.Probability.Distributions.Rademacher.RademacherEsscherBound

/-!
# Profile reduction of the tilted Rademacher tail

This file turns the quantitative normal-approximation input into the
one-dimensional profile bound used by the sparse one-row certificate.  It
separates the exact Esscher/Gaussian cancellation from the entropy, variance,
and Lyapunov profile inequalities `(O3)`--`(O5)`.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace Probability

/--
Raw `(O6)` form: after the Gaussian Mills cancellation, the only remaining
dependence on the tilted law is through its standard deviation and Lyapunov
ratio.
-/
theorem rademacherUpperTail_toReal_le_profile_raw
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x C : ℝ}
    (hx : 0 < x)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hK :
      kolmogorovDistance
          (rademacherTiltedStandardizedLaw b x)
          (gaussianReal 0 1) ≤
        C * rademacherLyapunovRatio b x) :
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
      Real.exp
          ((∑ i, Real.log (Real.cosh (x * b i))) - x ^ 2) *
        ((Real.sqrt (2 * Real.pi) * x *
              rademacherTiltedStdDev b x)⁻¹ +
          2 * C * rademacherLyapunovRatio b x) := by
  let A : ℝ := ∑ i, Real.log (Real.cosh (x * b i))
  let m : ℝ := rademacherTiltedMean b x
  let s : ℝ := rademacherTiltedStdDev b x
  let L : ℝ := rademacherLyapunovRatio b x
  have hs : 0 < s :=
    sqrt_rademacherTiltedVariance_pos b x hnorm
  have hm : m ≤ x :=
    rademacherTiltedMean_le b hx hnorm
  have hbase :=
    rademacherUpperTail_toReal_le_of_standardized_kolmogorov
      b hx hnorm hK
  have hgaussian :=
    esscherGaussianTail_le_cancelled A x m hx hs hm
  rw [rademacherTiltPartition_eq_exp_sum_log_cosh] at hbase
  change
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
      Real.exp A *
        (Real.exp (-x * m + x ^ 2 * s ^ 2 / 2) *
            standardGaussianTail ((x - m) / s + x * s) +
          2 * (C * L) * Real.exp (-x ^ 2)) at hbase
  change
    Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
        standardGaussianTail ((x - m) / s + x * s) ≤
      Real.exp (A - x ^ 2) /
        (Real.sqrt (2 * Real.pi) * (x * s)) at hgaussian
  calc
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
        Real.exp A *
          (Real.exp (-x * m + x ^ 2 * s ^ 2 / 2) *
              standardGaussianTail ((x - m) / s + x * s) +
            2 * (C * L) * Real.exp (-x ^ 2)) := hbase
    _ = Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
            standardGaussianTail ((x - m) / s + x * s) +
          2 * C * L * Real.exp (A - x ^ 2) := by
      rw [mul_add]
      congr 1
      · rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      · rw [show Real.exp A * (2 * (C * L) * Real.exp (-x ^ 2)) =
            2 * C * L * (Real.exp A * Real.exp (-x ^ 2)) by ring,
          ← Real.exp_add]
        congr 2
    _ ≤ Real.exp (A - x ^ 2) /
            (Real.sqrt (2 * Real.pi) * (x * s)) +
          2 * C * L * Real.exp (A - x ^ 2) :=
      add_le_add hgaussian (le_refl _)
    _ = Real.exp (A - x ^ 2) *
        ((Real.sqrt (2 * Real.pi) * x * s)⁻¹ +
          2 * C * L) := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := by rfl

/--
The one-dimensional profile bound `(O7)`.

`B` is the fourth-root profile parameter: every `|bᵢ| ≤ B` and
`∑ bᵢ⁴ = B⁴`.  The statement stays root-free at its API boundary and is
therefore convenient both for duplicated sparse coefficients and for later
certificate substitution.
-/
theorem rademacherUpperTail_toReal_le_profile
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x C B : ℝ}
    (hx : 0 < x) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hbound : ∀ i, |b i| ≤ B)
    (hfourth : ∑ i, b i ^ 4 = B ^ 4)
    (hK :
      kolmogorovDistance
          (rademacherTiltedStandardizedLaw b x)
          (gaussianReal 0 1) ≤
        C * rademacherLyapunovRatio b x) :
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
      Real.exp (-x ^ 2 * (1 + B ^ 2) / 2) *
        Real.cosh (x * B) *
        (Real.cosh (x * B ^ 2) /
            (Real.sqrt (2 * Real.pi) * x) +
          2 * C * B ^ 2 * Real.cosh (x * B ^ 2) ^ 3) := by
  let A : ℝ := ∑ i, Real.log (Real.cosh (x * b i))
  let s : ℝ := rademacherTiltedStdDev b x
  let L : ℝ := rademacherLyapunovRatio b x
  let c : ℝ := Real.cosh (x * B ^ 2)
  let k : ℝ := Real.sqrt (2 * Real.pi) * x
  have hs : 0 < s :=
    sqrt_rademacherTiltedVariance_pos b x hnorm
  have hc : 0 < c := Real.cosh_pos _
  have hk : 0 < k := mul_pos (by positivity) hx
  have hL0 : 0 ≤ L :=
    rademacherLyapunovRatio_nonneg b x
  have hroot :
      Real.sqrt (∑ i, b i ^ 4) = B ^ 2 := by
    rw [hfourth]
    have hpow : B ^ 4 = (B ^ 2) ^ 2 := by ring
    rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg B)]
  have hA :
      A ≤ x ^ 2 / 2 - rademacherEntropyDefect (x * B) := by
    have hent :=
      sum_log_cosh_sub_quadratic_le b hx.le hB hbound hfourth
    have hsquare :
        ∑ i, (x * b i) ^ 2 = x ^ 2 := by
      simp only [mul_pow]
      rw [← Finset.mul_sum, hnorm, mul_one]
    have hent' :
        A - (∑ i, (x * b i) ^ 2) / 2 ≤
          -rademacherEntropyDefect (x * B) := by
      simpa only [A, Finset.sum_sub_distrib, Finset.sum_div] using hent
    rw [hsquare] at hent'
    linarith
  have hexp :
      Real.exp (A - x ^ 2) ≤
        Real.exp (-x ^ 2 / 2 -
          rademacherEntropyDefect (x * B)) := by
    rw [Real.exp_le_exp]
    linarith
  have hsLower :
      c⁻¹ ≤ s := by
    have h :=
      inv_cosh_sqrt_sum_fourth_le_sqrt_tiltedVariance b x hnorm
    simpa only [c, s, hroot, rademacherTiltedStdDev] using h
  have hsInv : s⁻¹ ≤ c := by
    have h := inv_anti₀ (inv_pos.mpr hc) hsLower
    simpa only [inv_inv] using h
  have hgaussian :
      (Real.sqrt (2 * Real.pi) * x * s)⁻¹ ≤ c / k := by
    change (k * s)⁻¹ ≤ c / k
    rw [mul_inv_rev, div_eq_mul_inv, mul_comm c k⁻¹]
    calc
      s⁻¹ * k⁻¹ ≤ c * k⁻¹ :=
        mul_le_mul_of_nonneg_right hsInv (inv_nonneg.mpr hk.le)
      _ = k⁻¹ * c := by ring
  have hLyapunov :
      L ≤ B ^ 2 * c ^ 3 := by
    have h := rademacherLyapunovRatio_le b x hnorm
    simpa only [L, c, hroot] using h
  have hbracket :
      (Real.sqrt (2 * Real.pi) * x * s)⁻¹ +
          2 * C * L ≤
        c / k + 2 * C * B ^ 2 * c ^ 3 := by
    have hcoef : 0 ≤ 2 * C :=
      mul_nonneg (by norm_num) hC
    have hscaled :=
      mul_le_mul_of_nonneg_left hLyapunov hcoef
    exact add_le_add hgaussian (by
      simpa only [mul_assoc] using hscaled)
  have hbracket0 :
      0 ≤ (Real.sqrt (2 * Real.pi) * x * s)⁻¹ +
        2 * C * L := by
    exact add_nonneg (inv_nonneg.mpr (by positivity))
      (mul_nonneg (mul_nonneg (by norm_num) hC) hL0)
  have hraw :=
    rademacherUpperTail_toReal_le_profile_raw b hx hnorm hK
  calc
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
      Real.exp (A - x ^ 2) *
        ((Real.sqrt (2 * Real.pi) * x * s)⁻¹ + 2 * C * L) := hraw
    _ ≤ Real.exp (-x ^ 2 / 2 -
          rademacherEntropyDefect (x * B)) *
        (c / k + 2 * C * B ^ 2 * c ^ 3) :=
      mul_le_mul hexp hbracket hbracket0 (Real.exp_nonneg _)
    _ = Real.exp (-x ^ 2 * (1 + B ^ 2) / 2) *
        Real.cosh (x * B) *
        (Real.cosh (x * B ^ 2) /
            (Real.sqrt (2 * Real.pi) * x) +
          2 * C * B ^ 2 * Real.cosh (x * B ^ 2) ^ 3) := by
      have hfactor :
          Real.exp (-x ^ 2 / 2 -
              rademacherEntropyDefect (x * B)) =
            Real.exp (-x ^ 2 * (1 + B ^ 2) / 2) *
              Real.cosh (x * B) := by
        unfold rademacherEntropyDefect
        have hexponent :
            -x ^ 2 / 2 -
                ((x * B) ^ 2 / 2 -
                  Real.log (Real.cosh (x * B))) =
            -x ^ 2 * (1 + B ^ 2) / 2 +
              Real.log (Real.cosh (x * B)) := by ring
        rw [hexponent, Real.exp_add,
          Real.exp_log (Real.cosh_pos _)]
      rw [hfactor]

end Probability
end CertifiedJL
