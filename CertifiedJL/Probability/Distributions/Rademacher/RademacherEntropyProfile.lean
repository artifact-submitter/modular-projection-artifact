/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.HyperbolicProfile

/-!
# The Rademacher entropy profile

For a Rademacher variable, the gap between the Gaussian quadratic
log-moment-generating function and the exact one is

`δ(v) = v² / 2 - log (cosh v)`.

The sparse one-row argument needs the fact that `δ(v) / v⁴` decreases for
positive `v`.  We prove this through the elementary `E`, `F`, and `G`
derivative chain from the paper, retaining the intermediate sign statements
as a reusable API.
-/

namespace CertifiedJL
namespace Probability

/-- The entropy defect between the Gaussian and Rademacher log-MGFs. -/
noncomputable def rademacherEntropyDefect (v : ℝ) : ℝ :=
  v ^ 2 / 2 - Real.log (Real.cosh v)

/-- The innermost auxiliary function in the entropy-profile derivative chain. -/
noncomputable def rademacherEntropyE (v : ℝ) : ℝ :=
  Real.tanh v - v * (1 - Real.tanh v ^ 2)

/-- The middle auxiliary function in the entropy-profile derivative chain. -/
noncomputable def rademacherEntropyF (v : ℝ) : ℝ :=
  v * (3 - Real.tanh v ^ 2) - 3 * Real.tanh v

/-- The outer auxiliary function controlling the entropy-ratio derivative. -/
noncomputable def rademacherEntropyG (v : ℝ) : ℝ :=
  v ^ 2 + v * Real.tanh v - 4 * Real.log (Real.cosh v)

/-- The entropy defect normalized by its fourth-order scale. -/
noncomputable def rademacherEntropyRatio (v : ℝ) : ℝ :=
  rademacherEntropyDefect v / v ^ 4

@[simp]
theorem rademacherEntropyDefect_zero :
    rademacherEntropyDefect 0 = 0 := by
  simp [rademacherEntropyDefect]

@[simp]
theorem rademacherEntropyE_zero :
    rademacherEntropyE 0 = 0 := by
  simp [rademacherEntropyE]

@[simp]
theorem rademacherEntropyF_zero :
    rademacherEntropyF 0 = 0 := by
  simp [rademacherEntropyF]

@[simp]
theorem rademacherEntropyG_zero :
    rademacherEntropyG 0 = 0 := by
  simp [rademacherEntropyG]

/-- The entropy defect has derivative `v - tanh v`. -/
theorem hasDerivAt_rademacherEntropyDefect (v : ℝ) :
    HasDerivAt rademacherEntropyDefect (v - Real.tanh v) v := by
  have hraw :=
    (((hasDerivAt_id v).pow 2).div_const 2).sub
      (hasDerivAt_log_cosh v)
  have hfun :
      (fun x : ℝ => (id ^ 2) x / 2) -
          (fun x : ℝ => Real.log (Real.cosh x)) =
        rademacherEntropyDefect := by
    funext x
    simp [rademacherEntropyDefect]
  rw [hfun] at hraw
  apply hraw.congr_deriv
  norm_num

/-- The entropy defect is monotone on the nonnegative axis. -/
theorem monotoneOn_rademacherEntropyDefect :
    MonotoneOn rademacherEntropyDefect (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · exact fun x _ =>
      (hasDerivAt_rademacherEntropyDefect x).continuousAt.continuousWithinAt
  · exact fun x _ =>
      (hasDerivAt_rademacherEntropyDefect x).hasDerivWithinAt
  · intro x hx
    exact sub_nonneg.mpr (tanh_le_self (interior_subset hx))

/-- The `E` derivative is manifestly nonnegative on the nonnegative axis. -/
theorem hasDerivAt_rademacherEntropyE (v : ℝ) :
    HasDerivAt rademacherEntropyE
      (2 * v * Real.tanh v * (1 - Real.tanh v ^ 2)) v := by
  have hq := hasDerivAt_tanh v
  have hraw :=
    hq.sub ((hasDerivAt_id v).mul
      ((hasDerivAt_const v 1).sub (hq.pow 2)))
  have hfun :
      Real.tanh - id * ((fun _ : ℝ => 1) - Real.tanh ^ 2) =
        rademacherEntropyE := by
    funext x
    simp [rademacherEntropyE]
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, one_mul]
  rw [← one_sub_tanh_sq v]
  ring

/-- The `F` derivative factors through `E`. -/
theorem hasDerivAt_rademacherEntropyF (v : ℝ) :
    HasDerivAt rademacherEntropyF
      (2 * Real.tanh v * rademacherEntropyE v) v := by
  have hq := hasDerivAt_tanh v
  have hraw :=
    (hasDerivAt_id v).mul
        ((hasDerivAt_const v 3).sub (hq.pow 2))
      |>.sub (hq.const_mul 3)
  have hfun :
      id * ((fun _ : ℝ => 3) - Real.tanh ^ 2) -
          (fun x : ℝ => 3 * Real.tanh x) =
        rademacherEntropyF := by
    funext x
    simp [rademacherEntropyF]
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, one_mul]
  rw [← one_sub_tanh_sq v]
  unfold rademacherEntropyE
  ring

/-- The `G` derivative is `F`. -/
theorem hasDerivAt_rademacherEntropyG (v : ℝ) :
    HasDerivAt rademacherEntropyG (rademacherEntropyF v) v := by
  have hraw :=
    (((hasDerivAt_id v).pow 2).add
      ((hasDerivAt_id v).mul (hasDerivAt_tanh v))).sub
        ((hasDerivAt_log_cosh v).const_mul 4)
  have hfun :
      id ^ 2 + id * Real.tanh -
          (fun x : ℝ => 4 * Real.log (Real.cosh x)) =
        rademacherEntropyG := by
    funext x
    simp [rademacherEntropyG]
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [id_eq, Nat.cast_ofNat, one_mul, mul_one]
  rw [← one_sub_tanh_sq v]
  unfold rademacherEntropyF
  ring

/-- `G = 4δ - vδ'`, the numerator governing the entropy-ratio derivative. -/
theorem four_mul_entropyDefect_sub_mul_deriv (v : ℝ) :
    4 * rademacherEntropyDefect v -
        v * (v - Real.tanh v) =
      rademacherEntropyG v := by
  unfold rademacherEntropyDefect rademacherEntropyG
  ring

/-- The innermost auxiliary function is nonnegative on `[0, ∞)`. -/
theorem rademacherEntropyE_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ rademacherEntropyE v := by
  have hmono : MonotoneOn rademacherEntropyE (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun x _ => (hasDerivAt_rademacherEntropyE x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_rademacherEntropyE x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hx.le) (tanh_nonneg hx.le))
        (sub_nonneg.mpr (Real.tanh_sq_lt_one x).le)
  simpa using hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hv) hv

/-- The middle auxiliary function is nonnegative on `[0, ∞)`. -/
theorem rademacherEntropyF_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ rademacherEntropyF v := by
  have hmono : MonotoneOn rademacherEntropyF (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun x _ => (hasDerivAt_rademacherEntropyF x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_rademacherEntropyF x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact mul_nonneg (mul_nonneg (by norm_num) (tanh_nonneg hx.le))
        (rademacherEntropyE_nonneg hx.le)
  simpa using hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hv) hv

/-- The outer auxiliary function is nonnegative on `[0, ∞)`. -/
theorem rademacherEntropyG_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ rademacherEntropyG v := by
  have hmono : MonotoneOn rademacherEntropyG (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun x _ => (hasDerivAt_rademacherEntropyG x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_rademacherEntropyG x).hasDerivWithinAt
    · intro x hx
      exact rademacherEntropyF_nonneg (interior_subset hx)
  simpa using hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hv) hv

/-- Derivative of the normalized entropy defect on the positive axis. -/
theorem hasDerivAt_rademacherEntropyRatio {v : ℝ} (hv : 0 < v) :
    HasDerivAt rademacherEntropyRatio
      (-rademacherEntropyG v / v ^ 5) v := by
  have hraw :=
    (hasDerivAt_rademacherEntropyDefect v).div
      ((hasDerivAt_id v).pow 4) (pow_ne_zero 4 hv.ne')
  have hfun :
      rademacherEntropyDefect / id ^ 4 =
        rademacherEntropyRatio := by
    funext x
    simp [rademacherEntropyRatio]
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, pow_succ]
  rw [← four_mul_entropyDefect_sub_mul_deriv]
  field_simp
  ring

/-- The normalized entropy defect decreases on `(0, ∞)`. -/
theorem antitoneOn_rademacherEntropyRatio :
    AntitoneOn rademacherEntropyRatio (Set.Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
  · exact fun x hx =>
      (hasDerivAt_rademacherEntropyRatio hx).continuousAt.continuousWithinAt
  · exact fun x hx =>
      (hasDerivAt_rademacherEntropyRatio (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioi 0 := interior_subset hx
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (rademacherEntropyG_nonneg hx'.le))
      (pow_nonneg hx'.le 5)

/-- The entropy defect is even. -/
theorem rademacherEntropyDefect_abs (v : ℝ) :
    rademacherEntropyDefect |v| = rademacherEntropyDefect v := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_nonpos hv]
    unfold rademacherEntropyDefect
    rw [Real.cosh_neg]
    ring

/--
Finite form of the entropy-profile comparison.

The parameter `B` is an abstract fourth-moment scale.  The hypotheses say
that it bounds every coefficient and that its fourth power is exactly the
sum of coefficient fourth powers.  This root-free formulation avoids making
the analytic lemma depend on a chosen implementation of `ρ^(1/4)`.
-/
theorem entropyDefect_scale_le_sum
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x B : ℝ}
    (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hbound : ∀ i, |b i| ≤ B)
    (hfourth : ∑ i, b i ^ 4 = B ^ 4) :
    rademacherEntropyDefect (x * B) ≤
      ∑ i, rademacherEntropyDefect (x * b i) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases hB.eq_or_lt with rfl | hB
  · have hbzero : ∀ i, b i = 0 := by
      intro i
      have habs : |b i| = 0 :=
        le_antisymm (hbound i) (abs_nonneg (b i))
      exact abs_eq_zero.mp habs
    simp [hbzero]
  have hpoint :
      ∀ i, rademacherEntropyRatio (x * B) * (x * |b i|) ^ 4 ≤
        rademacherEntropyDefect (x * b i) := by
    intro i
    by_cases hbi : b i = 0
    · simp [hbi]
    · have habs : 0 < |b i| := abs_pos.mpr hbi
      have hsmall_pos : 0 < x * |b i| := mul_pos hx habs
      have hlarge_pos : 0 < x * B := mul_pos hx hB
      have hscale :
          rademacherEntropyRatio (x * B) ≤
            rademacherEntropyRatio (x * |b i|) :=
        antitoneOn_rademacherEntropyRatio hsmall_pos hlarge_pos
          (mul_le_mul_of_nonneg_left (hbound i) hx.le)
      have hmul :=
        mul_le_mul_of_nonneg_right hscale (pow_nonneg hsmall_pos.le 4)
      calc
        rademacherEntropyRatio (x * B) * (x * |b i|) ^ 4
            ≤ rademacherEntropyRatio (x * |b i|) * (x * |b i|) ^ 4 :=
          hmul
        _ = rademacherEntropyDefect (x * |b i|) := by
          unfold rademacherEntropyRatio
          field_simp
        _ = rademacherEntropyDefect (x * b i) := by
          rw [show x * |b i| = |x * b i| by
            simp only [abs_mul, abs_of_nonneg hx.le]]
          exact rademacherEntropyDefect_abs (x * b i)
  have hscaledFourth :
      ∑ i, (x * |b i|) ^ 4 = (x * B) ^ 4 := by
    simp only [mul_pow]
    rw [← Finset.mul_sum, ← hfourth]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    calc
      |b i| ^ 4 = (|b i| ^ 2) ^ 2 := by ring
      _ = ((b i) ^ 2) ^ 2 := by rw [sq_abs]
      _ = b i ^ 4 := by ring
  calc
    rademacherEntropyDefect (x * B) =
        rademacherEntropyRatio (x * B) * (x * B) ^ 4 := by
      unfold rademacherEntropyRatio
      field_simp
    _ = rademacherEntropyRatio (x * B) *
        ∑ i, (x * |b i|) ^ 4 := by rw [hscaledFourth]
    _ = ∑ i, rademacherEntropyRatio (x * B) * (x * |b i|) ^ 4 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i, rademacherEntropyDefect (x * b i) := by
      apply Finset.sum_le_sum
      intro i _
      exact hpoint i

/--
The exact finite inequality `(O3)` in log-MGF form.
-/
theorem sum_log_cosh_sub_quadratic_le
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x B : ℝ}
    (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hbound : ∀ i, |b i| ≤ B)
    (hfourth : ∑ i, b i ^ 4 = B ^ 4) :
    (∑ i, (Real.log (Real.cosh (x * b i)) -
        (x * b i) ^ 2 / 2)) ≤
      -rademacherEntropyDefect (x * B) := by
  have h := entropyDefect_scale_le_sum b hx hB hbound hfourth
  rw [← neg_le_neg_iff] at h
  simpa only [rademacherEntropyDefect, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, neg_sub] using h

end Probability
end CertifiedJL
