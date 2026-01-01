/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Vectors.Real
import CertifiedJL.Analysis.Fourier.ElementaryTrigBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Elementary cosine bounds

Endpoint-independent pointwise cosine and Euclidean-coordinate bounds.
-/

open Set

namespace CertifiedJL.Probability

theorem cos_le_exp_neg_sq_div_two {x : ℝ}
    (hx : |x| < Real.pi / 2) :
    Real.cos x ≤ Real.exp (-(x ^ 2) / 2) := by
  wlog hx0 : 0 ≤ x generalizing x
  · have hneg0 : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx0)
    have hnegBand : |-x| < Real.pi / 2 := by simpa using hx
    simpa [Real.cos_neg] using this hnegBand hneg0
  let f : ℝ → ℝ :=
    (fun y => Real.log (Real.cos y)) + fun y => y ^ 2 / 2
  have hxlt : x < Real.pi / 2 := (abs_lt.mp hx).2
  have hcont : ContinuousOn f (Icc 0 x) := by
    intro y hy
    have hylt : y < Real.pi / 2 := hy.2.trans_lt hxlt
    have hcos : 0 < Real.cos y :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hy.1, Real.pi_pos], hylt⟩
    exact (((Real.hasDerivAt_cos y).continuousAt.log hcos.ne').add
      ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc 0 x)) := by
    intro y hy
    rw [interior_Icc] at hy
    have hylt : y < Real.pi / 2 := hy.2.trans hxlt
    have hcos : 0 < Real.cos y :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hy.1, Real.pi_pos], hylt⟩
    exact (((Real.hasDerivAt_cos y).differentiableAt.log hcos.ne').add
      ((differentiableAt_id.pow 2).div_const 2)).differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Icc 0 x), deriv f y ≤ 0 := by
    intro y hy
    rw [interior_Icc] at hy
    have hy0 : 0 ≤ y := hy.1.le
    have hylt : y < Real.pi / 2 := hy.2.trans hxlt
    have hcos : 0 < Real.cos y :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hy.1, Real.pi_pos], hylt⟩
    have hlog := (Real.hasDerivAt_cos y).log hcos.ne'
    have hquad : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y := by
      simpa [div_eq_mul_inv, mul_comm] using
        (hasDerivAt_pow 2 y).const_mul (1 / 2 : ℝ)
    have hf' : deriv f y = -Real.tan y + y := by
      have hf2 : HasDerivAt f (-Real.sin y / Real.cos y + y) y := by
        exact hlog.add hquad
      rw [hf2.deriv, Real.tan_eq_sin_div_cos]
      rw [neg_div]
    rw [hf']
    linarith [Real.le_tan hy0 hylt]
  have hanti : AntitoneOn f (Icc 0 x) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 x) hcont hdiff hderiv
  have hfx : f x ≤ f 0 := hanti (left_mem_Icc.mpr hx0)
    (right_mem_Icc.mpr hx0) hx0
  have hlog : Real.log (Real.cos x) ≤ -(x ^ 2) / 2 := by
    dsimp [f] at hfx
    norm_num at hfx
    linarith
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
  calc
    Real.cos x = Real.exp (Real.log (Real.cos x)) :=
      (Real.exp_log hcos).symm
    _ ≤ Real.exp (-(x ^ 2) / 2) := Real.exp_le_exp.mpr hlog

end CertifiedJL.Probability

namespace CertifiedJL

theorem abs_coord_le_norm {d : ℕ}
    (w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |w i| ≤ ‖w‖ := by
  have hsq : (w i) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (w j))
      (Finset.mem_univ i)
  have habs : |w i| ^ 2 = (w i) ^ 2 := sq_abs (w i)
  nlinarith [abs_nonneg (w i), norm_nonneg w]

theorem cos_sq_le_exp_neg_sq {x : ℝ}
    (hx : |x| < Real.pi / 2) :
    Real.cos x ^ 2 ≤ Real.exp (-(x ^ 2)) := by
  have hcos0 : 0 ≤ Real.cos x :=
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).le
  have h := Probability.cos_le_exp_neg_sq_div_two hx
  have hsq := pow_le_pow_left₀ hcos0 h 2
  calc
    Real.cos x ^ 2 ≤ Real.exp (-(x ^ 2) / 2) ^ 2 := hsq
    _ = Real.exp (-(x ^ 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end CertifiedJL
