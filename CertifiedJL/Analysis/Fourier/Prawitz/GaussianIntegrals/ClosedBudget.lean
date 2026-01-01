/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Prawitz.GaussianIntegrals.Core

/-!
# Cutoff feasibility for the closed Prawitz Gaussian budget

This file isolates the feasibility diagnosis for the two closed Gaussian
contributions in the explicit norm-split bound.
-/

namespace CertifiedJL
namespace Probability

/--
The two closed Gaussian contributions in the explicit norm-split bound.
-/
noncomputable def prawitzGaussianClosedBudget
    (U₀ U : ℝ) : ℝ :=
  U₀ / U +
    (37 / 96 : ℝ) * Real.pi ^ 2 * U₀ ^ 2 / U ^ 2 +
    Real.exp (-(U₀ ^ 2) / 2) /
      (Real.pi * U₀ ^ 2)

/--
No cutoff satisfying the currently proved Tyurin crossover
`4 L U ≤ 1` can make even the two closed Gaussian terms fit inside the
target coefficient `16/25`.

This theorem is a formal feasibility diagnosis for the present
uniform-height closure of the norm-split inequality.  It does not rule out
the exact Gaussian-weighted Prawitz integral.  Rather, it shows that this
closure, combined with the existing crossover estimate, cannot complete the
target bound.  A successful argument must retain more of the Gaussian weight
or cancellation, use a genuinely global outer characteristic-function
envelope, or do both.
-/
theorem sixteen_twentyfifths_mul_lt_prawitzGaussianClosedBudget
    {L U₀ U : ℝ}
    (hL : 0 < L) (hLsmall : L ≤ 1 / 50)
    (hU₀ : 0 < U₀) (hU : 0 < U)
    (hcrossover : 4 * L * U ≤ 1) :
    (16 / 25 : ℝ) * L <
      prawitzGaussianClosedBudget U₀ U := by
  have hquad :
      0 ≤ (37 / 96 : ℝ) * Real.pi ^ 2 *
        U₀ ^ 2 / U ^ 2 := by
    positivity
  have htail :
      0 < Real.exp (-(U₀ ^ 2) / 2) /
        (Real.pi * U₀ ^ 2) := by
    positivity
  by_cases hlarge : (4 / 25 : ℝ) ≤ U₀
  · have hfourL : 4 * L ≤ 1 / U := by
      rw [le_div_iff₀ hU]
      exact hcrossover
    have hcore :
        (16 / 25 : ℝ) * L ≤ U₀ / U := by
      calc
        (16 / 25 : ℝ) * L =
            (4 / 25 : ℝ) * (4 * L) := by ring
        _ ≤ U₀ * (1 / U) := by
          exact mul_le_mul hlarge hfourL
            (by positivity) (by positivity)
        _ = U₀ / U := by ring
    unfold prawitzGaussianClosedBudget
    linarith
  · have hU₀lt : U₀ < 4 / 25 := lt_of_not_ge hlarge
    have hU₀sq : U₀ ^ 2 < (16 / 625 : ℝ) := by
      nlinarith [sq_nonneg (U₀ - 4 / 25)]
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hden :
        Real.pi * U₀ ^ 2 <
          1 - U₀ ^ 2 / 2 := by
      have hpiNonneg : 0 ≤ Real.pi := Real.pi_pos.le
      have hsqNonneg : 0 ≤ U₀ ^ 2 := sq_nonneg U₀
      have hmul :
          Real.pi * U₀ ^ 2 <
            4 * (16 / 625 : ℝ) := by
        calc
          Real.pi * U₀ ^ 2 ≤
              4 * U₀ ^ 2 :=
            mul_le_mul_of_nonneg_right hpi (sq_nonneg U₀)
          _ < 4 * (16 / 625 : ℝ) :=
            mul_lt_mul_of_pos_left hU₀sq (by norm_num)
      nlinarith
    have hexpLower :
        1 - U₀ ^ 2 / 2 ≤
          Real.exp (-(U₀ ^ 2) / 2) := by
      convert Real.add_one_le_exp (-(U₀ ^ 2) / 2) using 1
      all_goals ring
    have hdenExp :
        Real.pi * U₀ ^ 2 <
          Real.exp (-(U₀ ^ 2) / 2) :=
      hden.trans_le hexpLower
    have htailOne :
        1 < Real.exp (-(U₀ ^ 2) / 2) /
          (Real.pi * U₀ ^ 2) := by
      rw [lt_div_iff₀ (mul_pos Real.pi_pos
        (sq_pos_of_pos hU₀))]
      simpa only [one_mul] using hdenExp
    have htargetOne :
        (16 / 25 : ℝ) * L < 1 := by
      calc
        (16 / 25 : ℝ) * L ≤
            (16 / 25 : ℝ) * (1 / 50) := by
          exact mul_le_mul_of_nonneg_left hLsmall (by norm_num)
        _ < 1 := by norm_num
    unfold prawitzGaussianClosedBudget
    have hcoreNonneg : 0 ≤ U₀ / U := by positivity
    linarith

end Probability
end CertifiedJL
