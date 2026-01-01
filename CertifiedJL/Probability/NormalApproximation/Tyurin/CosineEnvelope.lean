/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Prawitz.KernelBounds
import CertifiedJL.Probability.NormalApproximation.Tyurin.ProductEnvelope
import Mathlib.Analysis.Convex.Deriv

/-!
# A certified cosine branch for Tyurin's product envelope

Tyurin's global characteristic-function estimate uses supporting tangents of

`x ↦ (1 - cos x) / x²`

between the switch point and `2π`.  This file proves a rationally weakened
version with factor `49 / 50`.  The two-percent loss leaves ample numerical
margin in the final Prawitz functional and turns the delicate endpoint
comparison into exact rational polynomial certificates.

The scalar theorem is unconditional in the coordinate frequency.  This is
important: a single tilted coordinate need not lie below the aggregate
Lyapunov frequency.
-/

open Set
open scoped BigOperators

namespace CertifiedJL
namespace Probability

universe u_1

variable {ι : Type u_1} [Fintype ι]

/-- The certified loss in the rational cosine branch. -/
noncomputable def tyurinCosineLoss : ℝ := 49 / 50

/-- The profile whose supporting tangents generate Tyurin's cosine branch. -/
noncomputable def tyurinCosineProfile : ℝ → ℝ :=
  ((fun _ : ℝ => (1 : ℝ)) - Real.cos) / (fun x : ℝ => x ^ 2)

/-- The derivative of `tyurinCosineProfile` away from zero. -/
noncomputable def tyurinCosineProfileSlope : ℝ → ℝ :=
  ((id * Real.sin) -
      ((fun _ : ℝ => (2 : ℝ)) *
        ((fun _ : ℝ => (1 : ℝ)) - Real.cos))) /
    (fun x : ℝ => x ^ 3)

/-- Numerator of the second derivative of `tyurinCosineProfile`. -/
noncomputable def tyurinCosineCurvatureNumerator (x : ℝ) : ℝ :=
  x ^ 2 * Real.cos x - 4 * x * Real.sin x +
    6 * (1 - Real.cos x)

/-- The second derivative of `tyurinCosineProfile` away from zero. -/
noncomputable def tyurinCosineProfileCurvature (x : ℝ) : ℝ :=
  tyurinCosineCurvatureNumerator x / x ^ 4

theorem hasDerivAt_tyurinCosineProfile
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt tyurinCosineProfile
      (tyurinCosineProfileSlope x) x := by
  unfold tyurinCosineProfile tyurinCosineProfileSlope
  change HasDerivAt
    (((fun _ : ℝ => (1 : ℝ)) - Real.cos) / fun x : ℝ => x ^ 2)
    ((x * Real.sin x - 2 * (1 - Real.cos x)) / x ^ 3) x
  have h :=
    ((hasDerivAt_const (𝕜 := ℝ) (x := x) (c := (1 : ℝ))).sub
        (Real.hasDerivAt_cos x)).div
      (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)
  have heq :
      (x * Real.sin x - 2 * (1 - Real.cos x)) / x ^ 3 =
        (Real.sin x * x ^ 2 -
            (1 - Real.cos x) * (2 * x)) /
          (x ^ 2) ^ 2 := by
    field_simp
  rw [heq]
  simpa only [sub_neg_eq_add, zero_add, Pi.sub_apply, Pi.one_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] using h

theorem hasDerivAt_tyurinCosineProfileSlope
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt tyurinCosineProfileSlope
      (tyurinCosineProfileCurvature x) x := by
  unfold tyurinCosineProfileSlope tyurinCosineProfileCurvature
  unfold tyurinCosineCurvatureNumerator
  have hnum :=
    ((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).sub
      ((hasDerivAt_const (𝕜 := ℝ) (x := x) (c := (2 : ℝ))).mul
        ((hasDerivAt_const (𝕜 := ℝ) (x := x) (c := (1 : ℝ))).sub
          (Real.hasDerivAt_cos x)))
  have h := hnum.div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx)
  apply h.congr_deriv
  simp only [Pi.sub_apply, Pi.mul_apply, sub_neg_eq_add, zero_add,
    zero_mul, id_eq, Nat.cast_ofNat, Nat.reduceSub]
  field_simp
  ring

private theorem tyurinCurvatureLowerPolynomial_nonneg
    {r : ℝ} (hr0 : (17 / 20 : ℝ) ≤ r)
    (hr1 : r ≤ 8 / 5) :
    0 ≤ 4 * (r - r ^ 3 / 6) -
      (r + 63 / 20) *
        (1 - r ^ 2 / 2 + r ^ 4 / 24) := by
  let z : ℝ := (r - 17 / 20) / (3 / 4)
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    norm_num at hr0 hr1 ⊢
    linarith
  have hrepr :
      4 * (r - r ^ 3 / 6) -
          (r + 63 / 20) *
            (1 - r ^ 2 / 2 + r ^ 4 / 24) =
        (334639 / 960000 : ℝ) * (1 - z) ^ 5 +
          5 * (83047277 / 76800000 : ℝ) *
            z * (1 - z) ^ 4 +
          10 * (549719 / 300000 : ℝ) *
            z ^ 2 * (1 - z) ^ 3 +
          10 * (6151633 / 2400000 : ℝ) *
            z ^ 3 * (1 - z) ^ 2 +
          5 * (60293 / 18750 : ℝ) *
            z ^ 4 * (1 - z) +
          (27767 / 7500 : ℝ) * z ^ 5 := by
    dsimp [z]
    ring
  rw [hrepr]
  positivity

theorem tyurinCosineCurvatureNumerator_nonneg
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 2 * Real.pi) :
    0 ≤ tyurinCosineCurvatureNumerator x := by
  have hxpos : 0 < x := by linarith
  have hsin : Real.sin x ≤ 0 := by
    rw [← Real.sin_sub_two_pi]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by linarith) (by linarith [Real.pi_lt_four])
  have hcosOne : Real.cos x ≤ 1 := Real.cos_le_one x
  rcases le_total x (3 * Real.pi / 2) with hxmid | hxmid
  · let r : ℝ := x - Real.pi
    have hr0 : 0 ≤ r := by
      dsimp [r]
      nlinarith [Real.pi_lt_four]
    have hrLower : (17 / 20 : ℝ) ≤ r := by
      dsimp [r]
      nlinarith [Real.pi_lt_d2]
    have hrUpper : r ≤ Real.pi / 2 := by
      dsimp [r]
      linarith
    have hrRat : r ≤ 8 / 5 := by
      nlinarith [Real.pi_lt_d2]
    have hsinLower := sin_taylor_three_le hr0 hrUpper
    have hcosUpper := cos_le_taylor_four hr0 hrUpper
    have hxUpper : x ≤ r + 63 / 20 := by
      dsimp [r]
      nlinarith [Real.pi_lt_d2]
    have hcosr0 : 0 ≤ Real.cos r :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) hrUpper
    have hpoly :=
      tyurinCurvatureLowerPolynomial_nonneg hrLower hrRat
    have hmain :
        0 ≤ 4 * Real.sin r - x * Real.cos r := by
      calc
        0 ≤ 4 * (r - r ^ 3 / 6) -
              (r + 63 / 20) *
                (1 - r ^ 2 / 2 + r ^ 4 / 24) := hpoly
        _ ≤ 4 * Real.sin r -
              (r + 63 / 20) *
                (1 - r ^ 2 / 2 + r ^ 4 / 24)
            := by
              gcongr
        _ ≤ 4 * Real.sin r -
              (r + 63 / 20) * Real.cos r := by
              have hfront : 0 ≤ r + 63 / 20 := by positivity
              nlinarith [mul_le_mul_of_nonneg_left hcosUpper hfront]
        _ ≤ 4 * Real.sin r - x * Real.cos r := by
              nlinarith [mul_le_mul_of_nonneg_right hxUpper hcosr0]
    have hsinShift : Real.sin x = -Real.sin r := by
      dsimp [r]
      linarith [Real.sin_sub_pi x]
    have hcosShift : Real.cos x = -Real.cos r := by
      dsimp [r]
      linarith [Real.cos_sub_pi x]
    unfold tyurinCosineCurvatureNumerator
    rw [hsinShift, hcosShift]
    have hscaled : 0 ≤ x * (4 * Real.sin r - x * Real.cos r) :=
      mul_nonneg hxpos.le hmain
    nlinarith [hcosr0]
  · have hcos0 : 0 ≤ Real.cos x := by
      rw [← Real.cos_sub_two_pi]
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith) (by linarith)
    unfold tyurinCosineCurvatureNumerator
    have hterm1 : 0 ≤ x ^ 2 * Real.cos x :=
      mul_nonneg (sq_nonneg x) hcos0
    have hterm2 : 0 ≤ -4 * x * Real.sin x := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hxpos.le hsin]
    have hterm3 : 0 ≤ 6 * (1 - Real.cos x) := by
      positivity
    linarith

theorem tyurinCosineProfileCurvature_nonneg
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 2 * Real.pi) :
    0 ≤ tyurinCosineProfileCurvature x := by
  unfold tyurinCosineProfileCurvature
  exact div_nonneg
    (tyurinCosineCurvatureNumerator_nonneg hx0 hx1)
    (by positivity)

private theorem tyurinCosineProfileSlope_mono :
    MonotoneOn tyurinCosineProfileSlope
      (Icc 4 (2 * Real.pi)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc 4 (2 * Real.pi))
  · intro x hx
    exact (hasDerivAt_tyurinCosineProfileSlope
      (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans_le hx.1)))
        |>.continuousAt.continuousWithinAt
  · intro x hx
    have hxi : x ∈ Ioo 4 (2 * Real.pi) := by
      simpa only [interior_Icc] using hx
    exact (hasDerivAt_tyurinCosineProfileSlope
      (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans hxi.1)))
        |>.hasDerivWithinAt
  · intro x hx
    have hxi : x ∈ Ioo 4 (2 * Real.pi) := by
      simpa only [interior_Icc] using hx
    exact tyurinCosineProfileCurvature_nonneg hxi.1.le hxi.2.le

theorem convexOn_tyurinCosineProfile :
    ConvexOn ℝ (Icc 4 (2 * Real.pi))
      tyurinCosineProfile := by
  apply MonotoneOn.convexOn_of_deriv
    (convex_Icc 4 (2 * Real.pi))
  · intro x hx
    exact (hasDerivAt_tyurinCosineProfile
      (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans_le hx.1)))
        |>.continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_tyurinCosineProfile
      (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans hx.1)))
        |>.differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hxi : x ∈ Ioo 4 (2 * Real.pi) := by
      simpa only [interior_Icc] using hx
    have hyi : y ∈ Ioo 4 (2 * Real.pi) := by
      simpa only [interior_Icc] using hy
    rw [(hasDerivAt_tyurinCosineProfile
        (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans hxi.1))).deriv,
      (hasDerivAt_tyurinCosineProfile
        (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans hyi.1))).deriv]
    exact tyurinCosineProfileSlope_mono
      (interior_subset hx) (interior_subset hy) hxy

theorem tyurinCosineProfile_tangent_le
    {y z : ℝ}
    (hy : y ∈ Icc 4 (2 * Real.pi))
    (hz : z ∈ Icc 4 (2 * Real.pi)) :
    tyurinCosineProfile z +
        tyurinCosineProfileSlope z * (y - z) ≤
      tyurinCosineProfile y := by
  rcases lt_trichotomy y z with hyz | rfl | hzy
  · have hs :=
      convexOn_tyurinCosineProfile.slope_le_of_hasDerivAt
        hy hz hyz
        (hasDerivAt_tyurinCosineProfile
          (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans_le hz.1)))
    rw [slope_def_field] at hs
    have hden : 0 < z - y := sub_pos.mpr hyz
    rw [div_le_iff₀ hden] at hs
    nlinarith
  · simp
  · have hs :=
      convexOn_tyurinCosineProfile.le_slope_of_hasDerivAt
        hz hy hzy
        (hasDerivAt_tyurinCosineProfile
          (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans_le hz.1)))
    rw [slope_def_field] at hs
    have hden : 0 < y - z := sub_pos.mpr hzy
    rw [le_div_iff₀ hden] at hs
    nlinarith

theorem tyurinCosineProfileSlope_nonpos
    {z : ℝ} (hz0 : 4 ≤ z) (hz1 : z ≤ 2 * Real.pi) :
    tyurinCosineProfileSlope z ≤ 0 := by
  have hsin : Real.sin z ≤ 0 := by
    rw [← Real.sin_sub_two_pi]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by linarith) (by linarith [Real.pi_lt_four])
  have hnum :
      z * Real.sin z - 2 * (1 - Real.cos z) ≤ 0 := by
    have hzpos : 0 ≤ z := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hzpos hsin,
      Real.cos_le_one z]
  unfold tyurinCosineProfileSlope
  change
    (z * Real.sin z - 2 * (1 - Real.cos z)) / z ^ 3 ≤ 0
  exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)

/--
The normalized cosine loss `(1 - cos x) / x²` decreases throughout
Tyurin's cosine band.  This endpoint monotonicity is useful for
cell certificates: after fixing the bandwidth at a cell's upper Lyapunov
endpoint, the cosine product envelope can be evaluated at that endpoint.
-/
theorem antitoneOn_tyurinCosineProfile :
    AntitoneOn tyurinCosineProfile (Icc 4 (2 * Real.pi)) := by
  apply antitoneOn_of_deriv_nonpos
    (convex_Icc 4 (2 * Real.pi))
  · intro x hx
    exact
      (hasDerivAt_tyurinCosineProfile
        (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans_le hx.1))).continuousAt
        |>.continuousWithinAt
  · rw [interior_Icc]
    intro x hx
    exact
      (hasDerivAt_tyurinCosineProfile
        (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans hx.1)))
        |>.differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(hasDerivAt_tyurinCosineProfile
      (ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans hx.1))).deriv]
    exact tyurinCosineProfileSlope_nonpos hx.1.le hx.2.le

private theorem sinTaylorFive_mono
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    x - x ^ 3 / 6 + x ^ 5 / 120 ≤
      y - y ^ 3 / 6 + y ^ 5 / 120 := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hx2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
  have hy2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
  have hxy1 : x * y ≤ 1 := by
    calc
      x * y ≤ 1 * y := mul_le_mul_of_nonneg_right hx1 hy0
      _ ≤ 1 := by simpa using hy1
  have hrepr :
      (y - y ^ 3 / 6 + y ^ 5 / 120) -
          (x - x ^ 3 / 6 + x ^ 5 / 120) =
        (y - x) *
          (1 - (y ^ 2 + y * x + x ^ 2) / 6 +
            (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 +
              y * x ^ 3 + x ^ 4) / 120) := by
    ring
  rw [← sub_nonneg, hrepr]
  apply mul_nonneg (sub_nonneg.mpr hxy)
  have hhigh :
      0 ≤ y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 +
        y * x ^ 3 + x ^ 4 := by positivity
  nlinarith

private theorem cosTaylorFour_anti
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    1 - y ^ 2 / 2 + y ^ 4 / 24 ≤
      1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hx2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
  have hy2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
  have hrepr :
      (1 - x ^ 2 / 2 + x ^ 4 / 24) -
          (1 - y ^ 2 / 2 + y ^ 4 / 24) =
        (y - x) * (x + y) *
          (1 / 2 - (x ^ 2 + y ^ 2) / 24) := by
    ring
  rw [← sub_nonneg, hrepr]
  have hcoef : 0 ≤ 1 / 2 - (x ^ 2 + y ^ 2) / 24 := by
    nlinarith
  exact mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx0 hy0))
    hcoef

private theorem sinTaylorSeven_mono
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤
      y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hxpow (n : ℕ) : x ^ n ≤ 1 := pow_le_one₀ hx0 hx1
  have hypow (n : ℕ) : y ^ n ≤ 1 := pow_le_one₀ hy0 hy1
  have hmixed (i j : ℕ) : y ^ i * x ^ j ≤ 1 := by
    calc
      y ^ i * x ^ j ≤ 1 * x ^ j :=
        mul_le_mul_of_nonneg_right (hypow i) (pow_nonneg hx0 j)
      _ ≤ 1 := by simpa using hxpow j
  have hrepr :
      (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) -
          (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) =
        (y - x) *
          (1 - (y ^ 2 + y * x + x ^ 2) / 6 +
            (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 +
              y * x ^ 3 + x ^ 4) / 120 -
            (y ^ 6 + y ^ 5 * x + y ^ 4 * x ^ 2 +
              y ^ 3 * x ^ 3 + y ^ 2 * x ^ 4 +
              y * x ^ 5 + x ^ 6) / 5040) := by
    ring
  rw [← sub_nonneg, hrepr]
  apply mul_nonneg (sub_nonneg.mpr hxy)
  have hsq :
      y ^ 2 + y * x + x ^ 2 ≤ 3 := by
    have hxy1 := hmixed 1 1
    norm_num at hxy1
    nlinarith [hxpow 2, hypow 2]
  have hfour :
      0 ≤ y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 +
        y * x ^ 3 + x ^ 4 := by positivity
  have hsix :
      y ^ 6 + y ^ 5 * x + y ^ 4 * x ^ 2 +
          y ^ 3 * x ^ 3 + y ^ 2 * x ^ 4 +
          y * x ^ 5 + x ^ 6 ≤ 7 := by
    nlinarith [hypow 6, hmixed 5 1, hmixed 4 2,
      hmixed 3 3, hmixed 2 4, hmixed 1 5, hxpow 6]
  nlinarith

private theorem cosineCentralTaylor_anti
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 8 / 5) :
    2 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 ≤
      2 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hxBound : x ^ 2 ≤ (64 / 25 : ℝ) := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxy),
      mul_nonneg hy0 (sub_nonneg.mpr hy)]
  have hyBound : y ^ 2 ≤ (64 / 25 : ℝ) := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy)]
  have hrepr :
      (2 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) -
          (2 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720) =
        (y - x) *
          ((x + y) * (1 / 2 - (x ^ 2 + y ^ 2) / 24) +
            (x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 +
              x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5) / 720) := by
    ring
  rw [← sub_nonneg, hrepr]
  apply mul_nonneg (sub_nonneg.mpr hxy)
  have hcoef : 0 ≤ 1 / 2 - (x ^ 2 + y ^ 2) / 24 := by
    nlinarith
  have hsum : 0 ≤ x + y := add_nonneg hx0 hy0
  have hhigh :
      0 ≤ x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 +
        x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5 := by
    positivity
  positivity

/-- Intercept of the supporting tangent at `z`. -/
noncomputable def tyurinCosineTangentA (z : ℝ) : ℝ :=
  (3 * (1 - Real.cos z) - z * Real.sin z) / z ^ 2

/-- Opposite slope of the supporting tangent at `z`. -/
noncomputable def tyurinCosineTangentB (z : ℝ) : ℝ :=
  (2 * (1 - Real.cos z) - z * Real.sin z) / z ^ 3

theorem tyurinCosineProfile_tangent_eq
    {y z : ℝ} (hz : z ≠ 0) :
    tyurinCosineProfile z +
        tyurinCosineProfileSlope z * (y - z) =
      tyurinCosineTangentA z - tyurinCosineTangentB z * y := by
  unfold tyurinCosineProfile tyurinCosineProfileSlope
  unfold tyurinCosineTangentA tyurinCosineTangentB
  change
    (1 - Real.cos z) / z ^ 2 +
        ((z * Real.sin z - 2 * (1 - Real.cos z)) / z ^ 3) *
          (y - z) =
      (3 * (1 - Real.cos z) - z * Real.sin z) / z ^ 2 -
        ((2 * (1 - Real.cos z) - z * Real.sin z) / z ^ 3) * y
  field_simp
  ring

theorem tyurinCosineTangentA_four_le :
    tyurinCosineTangentA 4 ≤ 2497 / 5000 := by
  let r : ℝ := 4 - Real.pi
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [Real.pi_lt_four]
  have hrLower : (1073 / 1250 : ℝ) ≤ r := by
    dsimp [r]
    nlinarith [Real.pi_lt_d4]
  have hrUpper : r ≤ (1717 / 2000 : ℝ) := by
    dsimp [r]
    nlinarith [Real.pi_gt_d4]
  have hrPi : r ≤ Real.pi / 2 := by
    dsimp [r]
    nlinarith [Real.pi_gt_three]
  have hsinTaylor := sin_le_taylor_five hr0 hrPi
  have hsinMono :=
    sinTaylorFive_mono hr0 hrUpper (by norm_num)
  have hsin :
      Real.sin r ≤
        (1717 / 2000 : ℝ) -
          (1717 / 2000 : ℝ) ^ 3 / 6 +
          (1717 / 2000 : ℝ) ^ 5 / 120 :=
    hsinTaylor.trans hsinMono
  have hcosTaylor := cos_le_taylor_four hr0 hrPi
  have hcosMono :=
    cosTaylorFour_anti (by norm_num : (0 : ℝ) ≤ 1073 / 1250)
      hrLower (hrUpper.trans (by norm_num))
  have hcos :
      Real.cos r ≤
        1 - (1073 / 1250 : ℝ) ^ 2 / 2 +
          (1073 / 1250 : ℝ) ^ 4 / 24 :=
    hcosTaylor.trans hcosMono
  have hsinShift : Real.sin 4 = -Real.sin r := by
    dsimp [r]
    linarith [Real.sin_sub_pi 4]
  have hcosShift : Real.cos 4 = -Real.cos r := by
    dsimp [r]
    linarith [Real.cos_sub_pi 4]
  unfold tyurinCosineTangentA
  rw [hsinShift, hcosShift]
  norm_num at hsin hcos ⊢
  linarith

theorem tyurinCosineTangentB_four_lower :
    989 / 10000 ≤ tyurinCosineTangentB 4 := by
  let r : ℝ := 4 - Real.pi
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [Real.pi_lt_four]
  have hrLower : (1073 / 1250 : ℝ) ≤ r := by
    dsimp [r]
    nlinarith [Real.pi_lt_d4]
  have hrUpper : r ≤ (1717 / 2000 : ℝ) := by
    dsimp [r]
    nlinarith [Real.pi_gt_d4]
  have hrPi : r ≤ Real.pi / 2 := by
    dsimp [r]
    nlinarith [Real.pi_gt_three]
  have hsinTaylor := sin_taylor_seven_le hr0 hrPi
  have hsinMono :=
    sinTaylorSeven_mono (by norm_num : (0 : ℝ) ≤ 1073 / 1250)
      hrLower (hrUpper.trans (by norm_num))
  have hsin :
      (1073 / 1250 : ℝ) -
          (1073 / 1250 : ℝ) ^ 3 / 6 +
          (1073 / 1250 : ℝ) ^ 5 / 120 -
          (1073 / 1250 : ℝ) ^ 7 / 5040 ≤
        Real.sin r :=
    hsinMono.trans hsinTaylor
  have hcosTaylor := cos_taylor_six_le hr0 hrPi
  have hcosMono :=
    cosineCentralTaylor_anti hr0 hrUpper (by norm_num)
  have hcos :
      1 - (1717 / 2000 : ℝ) ^ 2 / 2 +
          (1717 / 2000 : ℝ) ^ 4 / 24 -
          (1717 / 2000 : ℝ) ^ 6 / 720 ≤
        Real.cos r := by
    nlinarith [hcosMono, hcosTaylor]
  have hsinShift : Real.sin 4 = -Real.sin r := by
    dsimp [r]
    linarith [Real.sin_sub_pi 4]
  have hcosShift : Real.cos 4 = -Real.cos r := by
    dsimp [r]
    linarith [Real.cos_sub_pi 4]
  unfold tyurinCosineTangentB
  rw [hsinShift, hcosShift]
  norm_num at hsin hcos ⊢
  linarith

private theorem tyurinCosineLowPolynomial_nonneg
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 8 / 5) :
    0 ≤ (1 / 2 - 122353 / 250000 : ℝ) +
      (48461 / 500000 : ℝ) * y - y ^ 2 / 24 := by
  let z : ℝ := y / (8 / 5)
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    norm_num at hy1 ⊢
    linarith
  have hrepr :
      (1 / 2 - 122353 / 250000 : ℝ) +
          (48461 / 500000 : ℝ) * y - y ^ 2 / 24 =
        (2647 / 250000 : ℝ) * (1 - z) ^ 2 +
          2 * (110157 / 1250000 : ℝ) * z * (1 - z) +
          (221237 / 3750000 : ℝ) * z ^ 2 := by
    dsimp [z]
    ring
  rw [hrepr]
  positivity

private theorem tyurinCosineMiddleLeftPolynomial_nonneg
    {y : ℝ} (hy0 : (157 / 100 : ℝ) ≤ y)
    (hy1 : y ≤ 63 / 20) :
    0 ≤ 2 - (63 / 20 - y) ^ 2 / 2 +
        (63 / 20 - y) ^ 4 / 24 -
        (63 / 20 - y) ^ 6 / 720 -
      ((122353 / 250000 : ℝ) * y ^ 2 -
        (48461 / 500000 : ℝ) * y ^ 3) := by
  let z : ℝ := (y - 157 / 100) / (79 / 50)
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    norm_num at hy0 hy1 ⊢
    linarith
  have hrepr :
      2 - (63 / 20 - y) ^ 2 / 2 +
          (63 / 20 - y) ^ 4 / 24 -
          (63 / 20 - y) ^ 6 / 720 -
        ((122353 / 250000 : ℝ) * y ^ 2 -
          (48461 / 500000 : ℝ) * y ^ 3) =
        (3568175176243 / 22500000000000 : ℝ) *
            (1 - z) ^ 6 +
          6 * (233103896509 / 1125000000000 : ℝ) *
            z * (1 - z) ^ 5 +
          15 * (5611278168727 / 22500000000000 : ℝ) *
            z ^ 2 * (1 - z) ^ 4 +
          20 * (171209036293 / 625000000000 : ℝ) *
            z ^ 3 * (1 - z) ^ 3 +
          15 * (132664325717 / 500000000000 : ℝ) *
            z ^ 4 * (1 - z) ^ 2 +
          6 * (1126880521 / 5000000000 : ℝ) *
            z ^ 5 * (1 - z) +
          (692765387 / 4000000000 : ℝ) * z ^ 6 := by
    dsimp [z]
    ring
  rw [hrepr]
  positivity

private theorem tyurinCosineMiddleRightPolynomial_nonneg
    {y : ℝ} (hy0 : (157 / 50 : ℝ) ≤ y)
    (hy1 : y ≤ 4) :
    0 ≤ 2 - (y - 157 / 50) ^ 2 / 2 +
        (y - 157 / 50) ^ 4 / 24 -
        (y - 157 / 50) ^ 6 / 720 -
      ((122353 / 250000 : ℝ) * y ^ 2 -
        (48461 / 500000 : ℝ) * y ^ 3) := by
  let z : ℝ := (y - 157 / 50) / (43 / 50)
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    norm_num at hy0 hy1 ⊢
    linarith
  have hrepr :
      2 - (y - 157 / 50) ^ 2 / 2 +
          (y - 157 / 50) ^ 4 / 24 -
          (y - 157 / 50) ^ 6 / 720 -
        ((122353 / 250000 : ℝ) * y ^ 2 -
          (48461 / 500000 : ℝ) * y ^ 3) =
        (10950974973 / 62500000000 : ℝ) * (1 - z) ^ 6 +
          6 * (54597288619 / 375000000000 : ℝ) *
            z * (1 - z) ^ 5 +
          15 * (105189916019 / 937500000000 : ℝ) *
            z ^ 2 * (1 - z) ^ 4 +
          20 * (97659266073 / 1250000000000 : ℝ) *
            z ^ 3 * (1 - z) ^ 3 +
          15 * (2698263847 / 56250000000 : ℝ) *
            z ^ 4 * (1 - z) ^ 2 +
          6 * (12532081 / 450000000 : ℝ) *
            z ^ 5 * (1 - z) +
          (279518711951 / 11250000000000 : ℝ) * z ^ 6 := by
    dsimp [z]
    ring
  rw [hrepr]
  positivity

theorem tyurinRationalCubic_le_one_sub_cos
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 4) :
    (122353 / 250000 : ℝ) * y ^ 2 -
        (48461 / 500000 : ℝ) * y ^ 3 ≤
      1 - Real.cos y := by
  rcases le_total y (Real.pi / 2) with hsmall | hsmall
  · have hcos := cos_le_taylor_four hy0 hsmall
    have hyRat : y ≤ 8 / 5 := by
      nlinarith [Real.pi_lt_d2]
    have hpoly := tyurinCosineLowPolynomial_nonneg hy0 hyRat
    nlinarith [sq_nonneg y]
  · rcases le_total y Real.pi with hleft | hright
    · let x : ℝ := Real.pi - y
      let X : ℝ := 63 / 20 - y
      have hx0 : 0 ≤ x := by
        dsimp [x]
        linarith
      have hxPi : x ≤ Real.pi / 2 := by
        dsimp [x]
        linarith
      have hX0 : 0 ≤ X := by
        dsimp [X]
        nlinarith [Real.pi_lt_d2]
      have hxX : x ≤ X := by
        dsimp [x, X]
        nlinarith [Real.pi_lt_d2]
      have hXRat : X ≤ 8 / 5 := by
        dsimp [X]
        nlinarith [Real.pi_gt_d2]
      have hcentral := cosineCentralTaylor_anti hx0 hxX hXRat
      have hcosTaylor := cos_taylor_six_le hx0 hxPi
      have hcosShift : Real.cos y = -Real.cos x := by
        dsimp [x]
        linarith [Real.cos_pi_sub y]
      have hyLower : (157 / 100 : ℝ) ≤ y := by
        nlinarith [Real.pi_gt_d2]
      have hyUpper : y ≤ 63 / 20 := by
        nlinarith [Real.pi_lt_d2]
      have hpoly :=
        tyurinCosineMiddleLeftPolynomial_nonneg hyLower hyUpper
      dsimp [X] at hcentral
      nlinarith
    · let x : ℝ := y - Real.pi
      let X : ℝ := y - 157 / 50
      have hx0 : 0 ≤ x := by
        dsimp [x]
        linarith
      have hxPi : x ≤ Real.pi / 2 := by
        dsimp [x]
        nlinarith [hy1, Real.pi_gt_d2]
      have hX0 : 0 ≤ X := by
        dsimp [X]
        nlinarith [Real.pi_gt_d2]
      have hxX : x ≤ X := by
        dsimp [x, X]
        nlinarith [Real.pi_gt_d2]
      have hXRat : X ≤ 8 / 5 := by
        dsimp [X]
        nlinarith
      have hcentral := cosineCentralTaylor_anti hx0 hxX hXRat
      have hcosTaylor := cos_taylor_six_le hx0 hxPi
      have hcosShift : Real.cos y = -Real.cos x := by
        dsimp [x]
        linarith [Real.cos_sub_pi y]
      have hyLower : (157 / 50 : ℝ) ≤ y := by
        nlinarith [Real.pi_gt_d2]
      have hpoly :=
        tyurinCosineMiddleRightPolynomial_nonneg hyLower hy1
      dsimp [X] at hcentral
      nlinarith

theorem tyurinCosineLoss_mul_tangent_four_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 4) :
    tyurinCosineLoss *
        (tyurinCosineTangentA 4 * y ^ 2 -
          tyurinCosineTangentB 4 * y ^ 3) ≤
      1 - Real.cos y := by
  have hA :
      tyurinCosineTangentA 4 * y ^ 2 ≤
        (2497 / 5000 : ℝ) * y ^ 2 :=
    mul_le_mul_of_nonneg_right tyurinCosineTangentA_four_le
      (sq_nonneg y)
  have hB :
      (989 / 10000 : ℝ) * y ^ 3 ≤
        tyurinCosineTangentB 4 * y ^ 3 :=
    mul_le_mul_of_nonneg_right tyurinCosineTangentB_four_lower
      (by positivity)
  have htangent :
      tyurinCosineTangentA 4 * y ^ 2 -
          tyurinCosineTangentB 4 * y ^ 3 ≤
        (2497 / 5000 : ℝ) * y ^ 2 -
          (989 / 10000 : ℝ) * y ^ 3 := by
    linarith
  calc
    tyurinCosineLoss *
          (tyurinCosineTangentA 4 * y ^ 2 -
            tyurinCosineTangentB 4 * y ^ 3)
        ≤ tyurinCosineLoss *
            ((2497 / 5000 : ℝ) * y ^ 2 -
              (989 / 10000 : ℝ) * y ^ 3) := by
          exact mul_le_mul_of_nonneg_left htangent (by
            unfold tyurinCosineLoss
            norm_num)
    _ = (122353 / 250000 : ℝ) * y ^ 2 -
          (48461 / 500000 : ℝ) * y ^ 3 := by
          unfold tyurinCosineLoss
          ring
    _ ≤ 1 - Real.cos y :=
      tyurinRationalCubic_le_one_sub_cos hy0 hy1

private theorem tyurinCosineProfile_tangent_le_tangent_four
    {y z : ℝ} (hy1 : y ≤ 4)
    (hz0 : 4 ≤ z) (hz1 : z ≤ 2 * Real.pi) :
    tyurinCosineProfile z +
        tyurinCosineProfileSlope z * (y - z) ≤
      tyurinCosineProfile 4 +
        tyurinCosineProfileSlope 4 * (y - 4) := by
  have hfourMem : (4 : ℝ) ∈ Icc 4 (2 * Real.pi) := by
    constructor
    · rfl
    · nlinarith [Real.pi_gt_three]
  have hzMem : z ∈ Icc 4 (2 * Real.pi) := ⟨hz0, hz1⟩
  have htangentFour :=
    tyurinCosineProfile_tangent_le hfourMem hzMem
  have hslope :=
    tyurinCosineProfileSlope_mono hfourMem hzMem hz0
  have hmul :
      tyurinCosineProfileSlope z * (y - 4) ≤
        tyurinCosineProfileSlope 4 * (y - 4) :=
    mul_le_mul_of_nonpos_right hslope (sub_nonpos.mpr hy1)
  calc
    tyurinCosineProfile z +
          tyurinCosineProfileSlope z * (y - z) =
        (tyurinCosineProfile z +
          tyurinCosineProfileSlope z * (4 - z)) +
          tyurinCosineProfileSlope z * (y - 4) := by ring
    _ ≤ tyurinCosineProfile 4 +
          tyurinCosineProfileSlope z * (y - 4) := by
        linarith
    _ ≤ tyurinCosineProfile 4 +
          tyurinCosineProfileSlope 4 * (y - 4) := by
        linarith

private theorem tyurinCosineProfile_tangent_nonpos_of_two_pi_le
    {y z : ℝ} (hy : 2 * Real.pi ≤ y)
    (hz0 : 4 ≤ z) (hz1 : z ≤ 2 * Real.pi) :
    tyurinCosineProfile z +
        tyurinCosineProfileSlope z * (y - z) ≤ 0 := by
  have htwoPiMem :
      (2 * Real.pi : ℝ) ∈ Icc 4 (2 * Real.pi) := by
    constructor
    · nlinarith [Real.pi_gt_three]
    · rfl
  have hzMem : z ∈ Icc 4 (2 * Real.pi) := ⟨hz0, hz1⟩
  have htangent :=
    tyurinCosineProfile_tangent_le htwoPiMem hzMem
  have hprofileTwoPi : tyurinCosineProfile (2 * Real.pi) = 0 := by
    unfold tyurinCosineProfile
    change (1 - Real.cos (2 * Real.pi)) / (2 * Real.pi) ^ 2 = 0
    rw [Real.cos_two_pi]
    norm_num
  rw [hprofileTwoPi] at htangent
  have hslope :=
    tyurinCosineProfileSlope_nonpos hz0 hz1
  have hmul :
      tyurinCosineProfileSlope z * (y - 2 * Real.pi) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hslope (sub_nonneg.mpr hy)
  calc
    tyurinCosineProfile z +
          tyurinCosineProfileSlope z * (y - z) =
        (tyurinCosineProfile z +
          tyurinCosineProfileSlope z * (2 * Real.pi - z)) +
          tyurinCosineProfileSlope z * (y - 2 * Real.pi) := by ring
    _ ≤ 0 := by linarith

/--
The unconditional rational supporting-tangent estimate.  Unlike a
coordinatewise cutoff argument, it applies to every `y ≥ 0`, even when an
individual coordinate frequency exceeds the aggregate Lyapunov frequency
`z`.
-/
theorem tyurinCosineLoss_mul_tangent_le_one_sub_cos
    {y z : ℝ} (hy0 : 0 ≤ y)
    (hz0 : 4 ≤ z) (hz1 : z ≤ 2 * Real.pi) :
    tyurinCosineLoss *
        (tyurinCosineTangentA z * y ^ 2 -
          tyurinCosineTangentB z * y ^ 3) ≤
      1 - Real.cos y := by
  have hzNe : z ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans_le hz0)
  have hfactor :
      tyurinCosineTangentA z * y ^ 2 -
          tyurinCosineTangentB z * y ^ 3 =
        y ^ 2 *
          (tyurinCosineTangentA z -
            tyurinCosineTangentB z * y) := by ring
  rw [hfactor, ← tyurinCosineProfile_tangent_eq (y := y) hzNe,
    ← mul_assoc]
  rcases le_total y 4 with hy4 | hy4
  · have htangent :=
      tyurinCosineProfile_tangent_le_tangent_four
        hy4 hz0 hz1
    have hscaled :
        tyurinCosineLoss * y ^ 2 *
            (tyurinCosineProfile z +
              tyurinCosineProfileSlope z * (y - z)) ≤
          tyurinCosineLoss * y ^ 2 *
            (tyurinCosineProfile 4 +
              tyurinCosineProfileSlope 4 * (y - 4)) := by
      exact mul_le_mul_of_nonneg_left htangent
        (mul_nonneg
          (by unfold tyurinCosineLoss; norm_num)
          (sq_nonneg y))
    rw [tyurinCosineProfile_tangent_eq (y := y) (by norm_num : (4 : ℝ) ≠ 0)]
      at hscaled
    have hfour :=
      tyurinCosineLoss_mul_tangent_four_le hy0 hy4
    nlinarith
  · rcases le_total y (2 * Real.pi) with hyPi | hyPi
    · have hyMem : y ∈ Icc 4 (2 * Real.pi) := ⟨hy4, hyPi⟩
      have hzMem : z ∈ Icc 4 (2 * Real.pi) := ⟨hz0, hz1⟩
      have htangent :=
        tyurinCosineProfile_tangent_le hyMem hzMem
      let T : ℝ :=
        tyurinCosineProfile z +
          tyurinCosineProfileSlope z * (y - z)
      by_cases hT : 0 ≤ T
      · have hloss : tyurinCosineLoss ≤ 1 := by
          unfold tyurinCosineLoss
          norm_num
        have hscale : tyurinCosineLoss * T ≤ T :=
          mul_le_of_le_one_left hT hloss
        have hypos : 0 < y :=
          (by norm_num : (0 : ℝ) < 4).trans_le hy4
        have hprofile :
            tyurinCosineProfile y * y ^ 2 =
              1 - Real.cos y := by
          unfold tyurinCosineProfile
          change ((1 - Real.cos y) / y ^ 2) * y ^ 2 =
            1 - Real.cos y
          field_simp
        dsimp [T] at hT hscale ⊢
        nlinarith [mul_le_mul_of_nonneg_right htangent (sq_nonneg y)]
      · have hT' : T ≤ 0 := le_of_not_ge hT
        have hleft :
            tyurinCosineLoss * y ^ 2 * T ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg
              (by unfold tyurinCosineLoss; norm_num)
              (sq_nonneg y))
            hT'
        have hright : 0 ≤ 1 - Real.cos y := by
          linarith [Real.cos_le_one y]
        exact hleft.trans hright
    · have htangent :=
        tyurinCosineProfile_tangent_nonpos_of_two_pi_le
          hyPi hz0 hz1
      have hleft :
          tyurinCosineLoss * y ^ 2 *
              (tyurinCosineProfile z +
                tyurinCosineProfileSlope z * (y - z)) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg
            (by unfold tyurinCosineLoss; norm_num)
            (sq_nonneg y))
          htangent
      have hright : 0 ≤ 1 - Real.cos y := by
        linarith [Real.cos_le_one y]
      exact hleft.trans hright

theorem tyurinCosineTangentB_nonneg
    {z : ℝ} (hz0 : 4 ≤ z) (hz1 : z ≤ 2 * Real.pi) :
    0 ≤ tyurinCosineTangentB z := by
  have hslope := tyurinCosineProfileSlope_nonpos hz0 hz1
  have hzNe : z ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 4).trans_le hz0)
  unfold tyurinCosineProfileSlope at hslope
  unfold tyurinCosineTangentB
  change
    0 ≤ (2 * (1 - Real.cos z) - z * Real.sin z) / z ^ 3
  change
    (z * Real.sin z - 2 * (1 - Real.cos z)) / z ^ 3 ≤ 0
      at hslope
  have heq :
      (2 * (1 - Real.cos z) - z * Real.sin z) / z ^ 3 =
        -((z * Real.sin z - 2 * (1 - Real.cos z)) / z ^ 3) := by
    ring
  rw [heq]
  exact neg_nonneg.mpr hslope

theorem norm_centeredBiasedSignChar_le_exp_cosine
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t‖ ≤
      Real.exp
        (-((1 - Real.tanh u ^ 2) *
          (1 - Real.cos (2 * (t * a)))) / 4) := by
  let q : ℝ := 1 - Real.tanh u ^ 2
  let d : ℝ := q * (1 - Real.cos (2 * (t * a))) / 2
  have hq0 : 0 ≤ q :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hcos0 : 0 ≤ 1 - Real.cos (2 * (t * a)) := by
    linarith [Real.cos_le_one (2 * (t * a))]
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hsq :
      ‖centeredBiasedSignChar u a t‖ ^ 2 = 1 - d := by
    rw [norm_centeredBiasedSignChar_sq_eq_one_sub]
    rw [show Real.sin (t * a) ^ 2 =
        (1 - Real.cos (2 * (t * a))) / 2 by
      nlinarith [Real.cos_two_mul_eq_one_sub (t * a)]]
    dsimp [q, d]
    ring
  have honeExp : 1 - d ≤ Real.exp (-d) := by
    linarith [Real.add_one_le_exp (-d)]
  have hexpSq :
      Real.exp (-d) =
        Real.exp
          (-((1 - Real.tanh u ^ 2) *
            (1 - Real.cos (2 * (t * a)))) / 4) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [d, q]
    ring
  have hsqExp :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤
        Real.exp
          (-((1 - Real.tanh u ^ 2) *
            (1 - Real.cos (2 * (t * a)))) / 4) ^ 2 := by
    rw [← hexpSq, hsq]
    exact honeExp
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp hsqExp

theorem norm_prod_centeredBiasedSignChar_le_exp_cosineSum
    (u a : ι → ℝ) (t : ℝ) :
    ‖∏ i, centeredBiasedSignChar (u i) (a i) t‖ ≤
      Real.exp
        (-(∑ i,
          (1 - Real.tanh (u i) ^ 2) *
            (1 - Real.cos (2 * (t * a i)))) / 4) := by
  classical
  rw [norm_prod]
  calc
    ∏ i, ‖centeredBiasedSignChar (u i) (a i) t‖
        ≤ ∏ i, Real.exp
            (-((1 - Real.tanh (u i) ^ 2) *
              (1 - Real.cos (2 * (t * a i)))) / 4) := by
          apply Finset.prod_le_prod
          · intro i _
            exact norm_nonneg _
          · intro i _
            exact norm_centeredBiasedSignChar_le_exp_cosine
              (u i) (a i) t
    _ = Real.exp
          (∑ i,
            -((1 - Real.tanh (u i) ^ 2) *
              (1 - Real.cos (2 * (t * a i)))) / 4) := by
          rw [Real.exp_sum]
    _ = _ := by
          congr 1
          rw [← Finset.sum_neg_distrib, ← Finset.sum_div]

private theorem biasedSignCubicWeight_le_thirdMoment
    (u a : ℝ) :
    (1 - Real.tanh u ^ 2) * |a| ^ 3 ≤
      biasedSignThirdMomentTerm u a := by
  have hq0 : 0 ≤ 1 - Real.tanh u ^ 2 :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hm : 1 ≤ 1 + Real.tanh u ^ 2 := by
    nlinarith [sq_nonneg (Real.tanh u)]
  unfold biasedSignThirdMomentTerm
  rw [show 1 - Real.tanh u ^ 4 =
      (1 - Real.tanh u ^ 2) *
        (1 + Real.tanh u ^ 2) by ring]
  nlinarith [mul_le_mul_of_nonneg_left hm hq0,
    pow_nonneg (abs_nonneg a) 3]

theorem tyurinCosineAggregate_lower
    (u a : ι → ℝ) {t L : ℝ}
    (hL : 0 < L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L)
    (hfreq0 : 4 ≤ 2 * L * |t|)
    (hfreq1 : 2 * L * |t| ≤ 2 * Real.pi) :
    tyurinCosineLoss / L ^ 2 *
        (1 - Real.cos (2 * L * |t|)) ≤
      ∑ i,
        (1 - Real.tanh (u i) ^ 2) *
          (1 - Real.cos (2 * (t * a i))) := by
  classical
  let q : ι → ℝ := fun i => 1 - Real.tanh (u i) ^ 2
  let Y : ι → ℝ := fun i => 2 * |t * a i|
  let z : ℝ := 2 * L * |t|
  let S₃ : ℝ := ∑ i, q i * |a i| ^ 3
  have hq0 (i : ι) : 0 ≤ q i := by
    dsimp [q]
    exact sub_nonneg.mpr (Real.tanh_sq_lt_one (u i)).le
  have hY0 (i : ι) : 0 ≤ Y i := by
    dsimp [Y]
    positivity
  have hcosY (i : ι) :
      Real.cos (Y i) = Real.cos (2 * (t * a i)) := by
    dsimp [Y]
    rw [show 2 * |t * a i| = |2 * (t * a i)| by
      rw [abs_mul]
      norm_num]
    exact Real.cos_abs _
  have hcoord (i : ι) :
      tyurinCosineLoss *
          (tyurinCosineTangentA z * (Y i) ^ 2 -
            tyurinCosineTangentB z * (Y i) ^ 3) ≤
        1 - Real.cos (2 * (t * a i)) := by
    rw [← hcosY i]
    exact tyurinCosineLoss_mul_tangent_le_one_sub_cos
      (hY0 i) hfreq0 hfreq1
  have hweighted (i : ι) :
      q i * (tyurinCosineLoss *
          (tyurinCosineTangentA z * (Y i) ^ 2 -
            tyurinCosineTangentB z * (Y i) ^ 3)) ≤
        q i * (1 - Real.cos (2 * (t * a i))) :=
    mul_le_mul_of_nonneg_left (hcoord i) (hq0 i)
  have hsumCoord :
      ∑ i, q i * (tyurinCosineLoss *
          (tyurinCosineTangentA z * (Y i) ^ 2 -
            tyurinCosineTangentB z * (Y i) ^ 3)) ≤
        ∑ i, q i * (1 - Real.cos (2 * (t * a i))) :=
    Finset.sum_le_sum fun i _ => hweighted i
  have hvarq : ∑ i, q i * a i ^ 2 = 1 := by
    simpa only [q, biasedSignVarianceTerm, mul_comm] using hvar
  have hsqSum :
      ∑ i, q i * (Y i) ^ 2 = 4 * |t| ^ 2 := by
    calc
      ∑ i, q i * (Y i) ^ 2 =
          ∑ i, 4 * |t| ^ 2 * (q i * a i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp [Y]
            rw [abs_mul, mul_pow, mul_pow, sq_abs (a i)]
            ring
      _ = 4 * |t| ^ 2 * (∑ i, q i * a i ^ 2) := by
            rw [Finset.mul_sum]
      _ = 4 * |t| ^ 2 := by rw [hvarq, mul_one]
  have hcubeSum :
      ∑ i, q i * (Y i) ^ 3 = 8 * |t| ^ 3 * S₃ := by
    calc
      ∑ i, q i * (Y i) ^ 3 =
          ∑ i, 8 * |t| ^ 3 * (q i * |a i| ^ 3) := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp [Y]
            rw [abs_mul, mul_pow]
            ring
      _ = 8 * |t| ^ 3 * (∑ i, q i * |a i| ^ 3) := by
            rw [Finset.mul_sum]
      _ = 8 * |t| ^ 3 * S₃ := rfl
  have hleftEq :
      (∑ i, q i * (tyurinCosineLoss *
          (tyurinCosineTangentA z * (Y i) ^ 2 -
            tyurinCosineTangentB z * (Y i) ^ 3))) =
        tyurinCosineLoss *
          (tyurinCosineTangentA z * (4 * |t| ^ 2) -
            tyurinCosineTangentB z * (8 * |t| ^ 3 * S₃)) := by
    calc
      (∑ i, q i * (tyurinCosineLoss *
          (tyurinCosineTangentA z * (Y i) ^ 2 -
            tyurinCosineTangentB z * (Y i) ^ 3))) =
          tyurinCosineLoss * tyurinCosineTangentA z *
              (∑ i, q i * (Y i) ^ 2) -
            tyurinCosineLoss * tyurinCosineTangentB z *
              (∑ i, q i * (Y i) ^ 3) := by
                rw [Finset.mul_sum, Finset.mul_sum,
                  ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
      _ = _ := by rw [hsqSum, hcubeSum]; ring
  have hS₃L : S₃ ≤ L := by
    rw [← hthird]
    unfold S₃
    apply Finset.sum_le_sum
    intro i _
    exact biasedSignCubicWeight_le_thirdMoment (u i) (a i)
  have hB0 : 0 ≤ tyurinCosineTangentB z :=
    tyurinCosineTangentB_nonneg hfreq0 hfreq1
  have hthirdScaled :
      tyurinCosineTangentB z * (8 * |t| ^ 3 * S₃) ≤
        tyurinCosineTangentB z * (8 * |t| ^ 3 * L) := by
    apply mul_le_mul_of_nonneg_left _ hB0
    exact mul_le_mul_of_nonneg_left hS₃L (by positivity)
  have hreplace :
      tyurinCosineLoss *
          (tyurinCosineTangentA z * (4 * |t| ^ 2) -
            tyurinCosineTangentB z * (8 * |t| ^ 3 * L)) ≤
        tyurinCosineLoss *
          (tyurinCosineTangentA z * (4 * |t| ^ 2) -
            tyurinCosineTangentB z * (8 * |t| ^ 3 * S₃)) := by
    apply mul_le_mul_of_nonneg_left _ (by
      unfold tyurinCosineLoss
      norm_num)
    linarith
  have hformula :
      tyurinCosineLoss / L ^ 2 *
          (1 - Real.cos z) =
        tyurinCosineLoss *
          (tyurinCosineTangentA z * (4 * |t| ^ 2) -
            tyurinCosineTangentB z * (8 * |t| ^ 3 * L)) := by
    have htAbs : |t| ≠ 0 := by
      intro ht
      rw [ht] at hfreq0
      norm_num at hfreq0
    unfold tyurinCosineTangentA tyurinCosineTangentB
    dsimp [z]
    field_simp [hL.ne', htAbs]
    ring
  rw [show (∑ i,
      (1 - Real.tanh (u i) ^ 2) *
        (1 - Real.cos (2 * (t * a i)))) =
      ∑ i, q i * (1 - Real.cos (2 * (t * a i))) by rfl]
  rw [show 2 * L * |t| = z by rfl, hformula]
  exact hreplace.trans (hleftEq ▸ hsumCoord)

/--
The certified cosine branch of the global tilted-sign product envelope.
The factor `49 / 50` is the only loss relative to Tyurin's exact
supporting-tangent formula.
-/
theorem norm_prod_centeredBiasedSignChar_le_tyurinCosine
    (u a : ι → ℝ) {t L : ℝ}
    (hL : 0 < L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L)
    (hfreq0 : 4 ≤ 2 * L * |t|)
    (hfreq1 : 2 * L * |t| ≤ 2 * Real.pi) :
    ‖∏ i, centeredBiasedSignChar (u i) (a i) t‖ ≤
      Real.exp
        (-(tyurinCosineLoss / (4 * L ^ 2) *
          (1 - Real.cos (2 * L * |t|)))) := by
  have hproduct :=
    norm_prod_centeredBiasedSignChar_le_exp_cosineSum u a t
  have haggregate :=
    tyurinCosineAggregate_lower u a hL hvar hthird hfreq0 hfreq1
  calc
    ‖∏ i, centeredBiasedSignChar (u i) (a i) t‖
        ≤ Real.exp
            (-(∑ i,
              (1 - Real.tanh (u i) ^ 2) *
                (1 - Real.cos (2 * (t * a i)))) / 4) := hproduct
    _ ≤ Real.exp
          (-(tyurinCosineLoss / (4 * L ^ 2) *
            (1 - Real.cos (2 * L * |t|)))) := by
      apply Real.exp_le_exp.mpr
      calc
        -(∑ i,
            (1 - Real.tanh (u i) ^ 2) *
              (1 - Real.cos (2 * (t * a i)))) / 4
            ≤ -(tyurinCosineLoss / L ^ 2 *
                (1 - Real.cos (2 * L * |t|))) / 4 := by
              linarith
        _ = -(tyurinCosineLoss / (4 * L ^ 2) *
              (1 - Real.cos (2 * L * |t|))) := by ring
end Probability
end CertifiedJL
