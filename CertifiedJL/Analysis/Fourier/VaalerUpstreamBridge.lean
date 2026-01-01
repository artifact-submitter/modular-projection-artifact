/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author

This bridge uses the proof of Vaaler's minor wall from
`gersh/ternary-goldbach-lean`, commit
`89416190c037331d7ebc04cd62ddb974cfb4dfcf` (Apache-2.0),
copyright (c) 2026 Gershon Bialer.  The required source modules are vendored
under `Vendor/GershVaaler/` with their original Apache headers.
-/

import CertifiedJL.Analysis.Fourier.Beurling.HDerivative
import CertifiedJL.Analysis.Fourier.Beurling.JDecay
import Vendor.GershVaaler.MathExtras.NumberTheory.Analysis.VaalerMinorWallClosed

open MeasureTheory Real

namespace CertifiedJL
namespace Probability

namespace Upstream

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerMinorWallClosed

theorem tail_eq (x : ℝ) :
    tailSum x = beurlingReciprocalSquareTail x := by
  simp only [tailSum, beurlingReciprocalSquareTail, one_div,
    inv_pow]

theorem interpH_eq_beurlingH_of_pos
    {x : ℝ} (hx : 0 < x) :
    interpH x = beurlingH x := by
  rw [beurlingH_of_pos hx]
  by_cases hs : Real.sin (Real.pi * x) = 0
  · simp [interpH, hs, Real.sign_of_pos hx]
  · rw [interpH_rewrite
      MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds hs,
      tail_eq]
    simp only [inv_pow, div_eq_mul_inv]
    ring

theorem interpH_eq_beurlingH (x : ℝ) :
    interpH x = beurlingH x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    rw [← neg_neg x, interpH_neg,
      beurlingH_neg, interpH_eq_beurlingH_of_pos hpos]
  · simp [interpH, beurlingH_zero]
  · exact interpH_eq_beurlingH_of_pos hx

theorem jhat_eq_beurlingJHat (t : ℝ) :
    vaalerJhatCont t = beurlingJHat t := by
  by_cases hout : 1 ≤ |t|
  · simp [vaalerJhatCont, beurlingJHat, hout,
      not_lt.mpr hout]
  · have hin : |t| < 1 := not_le.mp hout
    by_cases ht : t = 0
    · subst t
      simp [vaalerJhatCont]
    · rw [beurlingJHat_of_ne_zero_of_abs_lt_one ht hin]
      simp only [vaalerJhatCont, if_neg hout, if_neg ht]
      unfold
        MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg.vaalerJhat
      rcases lt_or_gt_of_ne ht with htneg | htpos
      · rw [abs_of_neg htneg]
        rw [show Real.pi * -t = -(Real.pi * t) by ring]
        have hcot :
            Real.cot (-(Real.pi * t)) = -Real.cot (Real.pi * t) := by
          simp only [Real.cot, Complex.cot, Complex.ofReal_neg]
          rw [Complex.cos_neg, Complex.sin_neg, div_neg]
          simp
        rw [hcot]
        ring
      · rw [abs_of_pos htpos]

theorem vaalerJ_eq_beurlingJ :
    vaalerJ = beurlingJ := by
  rw [MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJ_eq_fourierInv_cont,
    beurlingJ_eq_fourierInv]
  congr 1
  funext t
  simp [MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont,
    beurlingJHatC,
    jhat_eq_beurlingJHat]

end Upstream

/--
Global Vaaler derivative identity for the canonical CertifiedJL functions.

This is the analytic heart of the sharp Prawitz smoothing inequality:
Beurling's band-limited interpolant has derivative twice the real part of
the inverse Fourier transform of the compact multiplier `beurlingJHat`.
-/
theorem hasDerivAt_beurlingH_two_mul_re_beurlingJ (x : ℝ) :
    HasDerivAt beurlingH (2 * (beurlingJ x).re) x := by
  have h :=
    MathExtras.NumberTheory.Analysis.VaalerMinorWallClosed.hasDerivAt_interpH_two_mul_re_vaalerJ x
  rw [Upstream.vaalerJ_eq_beurlingJ] at h
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y =>
      (Upstream.interpH_eq_beurlingH y).symm)

end Probability
end CertifiedJL
