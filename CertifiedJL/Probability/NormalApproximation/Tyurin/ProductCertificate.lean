/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.GlobalEnvelope
import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Polynomial envelopes for the cosine branch of Tyurin's product bound

The finite D-star certificate must not evaluate trigonometric functions.
On the single cosine lobe `4 ≤ x ≤ 2π`, we instead lower-bound
`1 - cos x` by one of two elementary polynomials.  The split at `3π/2`
keeps both polynomials close to the true function while leaving only
rational arithmetic and exponential enclosures to the checker.
-/

open Set

namespace CertifiedJL
namespace Probability

/--
On the left half of the lobe, reflect around `π` and use
`1 - y²/2 ≤ cos y`.
-/
theorem two_sub_sub_pi_sq_div_two_le_one_sub_cos
    (x : ℝ) :
    2 - (x - Real.pi) ^ 2 / 2 ≤ 1 - Real.cos x := by
  have hcos :
      1 - (x - Real.pi) ^ 2 / 2 ≤ Real.cos (x - Real.pi) :=
    Real.one_sub_sq_div_two_le_cos
  have hshift : Real.cos (x - Real.pi) = -Real.cos x :=
    Real.cos_sub_pi x
  rw [hshift] at hcos
  linarith

/--
On the right half of the lobe, reflect around `2π` and use the fourth-order
upper Taylor polynomial for cosine.
-/
theorem reflected_quartic_le_one_sub_cos
    {x : ℝ} (hleft : 3 * Real.pi / 2 ≤ x)
    (hright : x ≤ 2 * Real.pi) :
    let r := 2 * Real.pi - x
    r ^ 2 / 2 - r ^ 4 / 24 ≤ 1 - Real.cos x := by
  dsimp only
  let r : ℝ := 2 * Real.pi - x
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith
  have hrPi : r ≤ Real.pi / 2 := by
    dsimp [r]
    linarith
  have htaylor := cos_le_taylor_four hr0 hrPi
  have hshift : Real.cos r = Real.cos x := by
    dsimp [r]
    exact Real.cos_two_pi_sub x
  rw [hshift] at htaylor
  linarith

/--
The positive polynomial lower envelope used on Tyurin's cosine lobe.
-/
noncomputable def tyurinCosineCertificateLower (x : ℝ) : ℝ :=
  if x ≤ 3 * Real.pi / 2 then
    2 - (x - Real.pi) ^ 2 / 2
  else
    (2 * Real.pi - x) ^ 2 / 2 -
      (2 * Real.pi - x) ^ 4 / 24

theorem tyurinCosineCertificateLower_le_one_sub_cos
    {x : ℝ} (_hleft : 4 ≤ x) (hright : x ≤ 2 * Real.pi) :
    tyurinCosineCertificateLower x ≤ 1 - Real.cos x := by
  unfold tyurinCosineCertificateLower
  split_ifs with hsplit
  · exact two_sub_sub_pi_sq_div_two_le_one_sub_cos x
  · exact reflected_quartic_le_one_sub_cos
      (le_of_not_ge hsplit) hright

theorem tyurinCosineCertificateLower_nonneg
    {x : ℝ} (hleft : 4 ≤ x) (hright : x ≤ 2 * Real.pi) :
    0 ≤ tyurinCosineCertificateLower x := by
  unfold tyurinCosineCertificateLower
  split_ifs with hsplit
  · have hy0 : 0 ≤ x - Real.pi := by
      nlinarith [Real.pi_lt_four]
    have hy2 : x - Real.pi ≤ 2 := by
      nlinarith [Real.pi_lt_four]
    nlinarith [sq_nonneg (x - Real.pi),
      mul_self_le_mul_self hy0 hy2]
  · have hr0 : 0 ≤ 2 * Real.pi - x := by linarith
    have hr2 : 2 * Real.pi - x ≤ 2 := by
      have hx : 3 * Real.pi / 2 ≤ x := le_of_not_ge hsplit
      nlinarith [Real.pi_lt_four]
    have hrsq : (2 * Real.pi - x) ^ 2 ≤ 4 := by
      nlinarith [mul_self_le_mul_self hr0 hr2]
    nlinarith [sq_nonneg (2 * Real.pi - x),
      sq_nonneg ((2 * Real.pi - x) ^ 2)]

/--
Trigonometric-free upper bound for the cosine branch of the global product
envelope.
-/
theorem tyurinProductEnvelope_le_cosineCertificate
    {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u)
    (hleft : 4 ≤ 2 * L * u)
    (hright : 2 * L * u ≤ 2 * Real.pi) :
    tyurinProductEnvelope L u ≤
      Real.exp
        (-(tyurinCosineLoss / (4 * L ^ 2) *
          tyurinCosineCertificateLower (2 * L * u))) := by
  have hbranch0 :
      ¬(2 * L * |u| < tyurinRationalM) := by
    rw [abs_of_nonneg hu]
    unfold tyurinRationalM
    linarith
  have hbranch1 :
      2 * L * |u| ≤ 2 * Real.pi := by
    simpa [abs_of_nonneg hu] using hright
  rw [tyurinProductEnvelope, tyurinB, if_neg hbranch0,
    if_pos hbranch1]
  apply Real.exp_le_exp.mpr
  have hlower :=
    tyurinCosineCertificateLower_le_one_sub_cos hleft hright
  have hfactor :
      0 ≤ tyurinCosineLoss / (4 * L ^ 2) := by
    unfold tyurinCosineLoss
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hlower hfactor
  calc
    -2 * tyurinCosineLoss / (2 * L) ^ 2 *
          (1 - Real.cos (2 * L * u)) / 2 =
        -(tyurinCosineLoss / (4 * L ^ 2) *
          (1 - Real.cos (2 * L * u))) := by
            field_simp [hL.ne']
            ring
    _ ≤ -(tyurinCosineLoss / (4 * L ^ 2) *
          tyurinCosineCertificateLower (2 * L * u)) :=
      neg_le_neg hscaled

/-! ## Fully rational lower envelope -/

/--
A rational, trigonometric-free lower envelope on the portion
`4 ≤ x ≤ 157/25` used by the finite checker.  The narrow middle strip
separates the two Taylor coordinate systems without asking the checker to
compare a rational point with `3π/2`.
-/
noncomputable def tyurinRationalCosineLower (x : ℝ) : ℝ :=
  if x ≤ 471 / 100 then
    2 - (x - 157 / 50) ^ 2 / 2
  else if x < 189 / 40 then
    2 / 5
  else
    (157 / 25 - x) ^ 2 / 2 -
      (157 / 25 - x) ^ 4 / 24

private theorem quarticCosineLower_mono
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hR : R ≤ 8 / 5) :
    r ^ 2 / 2 - r ^ 4 / 24 ≤
      R ^ 2 / 2 - R ^ 4 / 24 := by
  have hR0 : 0 ≤ R := hr.trans hrR
  have hrsq : r ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ hr hR0).2 hrR
  have hsum :
      r ^ 2 + R ^ 2 ≤ 6 := by
    have hRsq : R ^ 2 ≤ (8 / 5 : ℝ) ^ 2 :=
      (sq_le_sq₀ hR0 (by norm_num)).2 hR
    nlinarith [sq_nonneg r]
  have hfactor :
      (R ^ 2 / 2 - R ^ 4 / 24) -
          (r ^ 2 / 2 - r ^ 4 / 24) =
        (R ^ 2 - r ^ 2) *
          (1 / 2 - (R ^ 2 + r ^ 2) / 24) := by
    ring
  rw [← sub_nonneg, hfactor]
  exact mul_nonneg (sub_nonneg.mpr hrsq) (by nlinarith)

theorem tyurinRationalCosineLower_le_one_sub_cos
    {x : ℝ} (hleft : 4 ≤ x) (hright : x ≤ 157 / 25) :
    tyurinRationalCosineLower x ≤ 1 - Real.cos x := by
  unfold tyurinRationalCosineLower
  split_ifs with hfirst hmiddle
  · have hy0 : 0 ≤ x - Real.pi := by
      nlinarith [Real.pi_lt_four]
    have hyrat0 : 0 ≤ x - 157 / 50 := by norm_num at hleft ⊢; linarith
    have hy :
        x - Real.pi ≤ x - 157 / 50 := by
      nlinarith [pi_gt_157_div_50]
    have hsq :
        (x - Real.pi) ^ 2 ≤ (x - 157 / 50) ^ 2 :=
      (sq_le_sq₀ hy0 hyrat0).2 hy
    exact (by
      nlinarith [two_sub_sub_pi_sq_div_two_le_one_sub_cos x])
  · have hxl : 471 / 100 < x := lt_of_not_ge hfirst
    have hxpi : x ≤ 2 * Real.pi := by
      nlinarith [pi_gt_157_div_50]
    have hcos :=
      Real.cos_le_one_sub_mul_cos_sq
        (x := x - 2 * Real.pi)
        (by
          rw [abs_sub_comm]
          exact abs_le.mpr
            ⟨by nlinarith [pi_gt_157_div_50],
              by nlinarith [pi_lt_63_div_20]⟩)
    have hshift : Real.cos (x - 2 * Real.pi) = Real.cos x :=
      Real.cos_sub_two_pi x
    rw [hshift] at hcos
    have hpiSq : Real.pi ^ 2 ≤ (63 / 20 : ℝ) ^ 2 :=
      (sq_le_sq₀ Real.pi_pos.le (by norm_num)).2
        (pi_lt_63_div_20.le)
    have hgap : (311 / 200 : ℝ) ≤ 2 * Real.pi - x := by
      nlinarith [pi_gt_157_div_50]
    have hgap0 : 0 ≤ 2 * Real.pi - x := by linarith
    have hgapSq :
        (311 / 200 : ℝ) ^ 2 ≤ (2 * Real.pi - x) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hgap0).2 hgap
    have hcoeff :
        (2 / 5 : ℝ) ≤
          2 / Real.pi ^ 2 * (2 * Real.pi - x) ^ 2 := by
      have hpiPos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ hpiPos]
      calc
        (2 / 5 : ℝ) * Real.pi ^ 2
            ≤ (2 / 5 : ℝ) * (63 / 20 : ℝ) ^ 2 := by
              gcongr
        _ ≤ 2 * (311 / 200 : ℝ) ^ 2 := by norm_num
        _ ≤ 2 * (2 * Real.pi - x) ^ 2 := by gcongr
    nlinarith
  · have hxLower : (189 / 40 : ℝ) ≤ x :=
      le_of_not_gt hmiddle
    let r : ℝ := 2 * Real.pi - x
    let q : ℝ := 157 / 25 - x
    have hq0 : 0 ≤ q := by
      dsimp [q]
      linarith
    have hqr : q ≤ r := by
      dsimp [q, r]
      nlinarith [pi_gt_157_div_50]
    have hr0 : 0 ≤ r := hq0.trans hqr
    have hrUpper : r ≤ Real.pi / 2 := by
      dsimp [r]
      nlinarith [pi_lt_63_div_20]
    have hrRat : r ≤ 8 / 5 := by
      nlinarith [Real.pi_lt_d2]
    have hxpi : x ≤ 2 * Real.pi := by
      nlinarith [pi_gt_157_div_50]
    have hmono :=
      quarticCosineLower_mono hq0 hqr hrRat
    have htaylor :=
      reflected_quartic_le_one_sub_cos
        (by nlinarith [pi_lt_63_div_20]) hxpi
    dsimp only at htaylor
    dsimp [q, r] at hmono
    exact hmono.trans htaylor

end Probability
end CertifiedJL
