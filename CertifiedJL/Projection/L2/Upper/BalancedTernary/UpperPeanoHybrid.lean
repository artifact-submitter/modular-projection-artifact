/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFourthOrder
import CertifiedJL.Analysis.Peano.PeanoGaussianKSecond

/-! # Exact finite-sum assembly for the sparse upper Peano hybrid -/

open scoped BigOperators

namespace CertifiedJL

/-- The two one-coordinate Peano estimates assemble with exactly the U7
constants.  The sign in the Gaussian-to-K term is explicit in the proof. -/
theorem norm_fourthPeanoHybridRemainder_le
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (G0 R0 G4 : ℂ) (K4 Gcoord4 : ι → ℂ) (D6 D8 : ℝ)
    (hfirst : G0 - R0 =
      ∑ i, (b i ^ 4 / 12 : ℝ) • K4 i)
    (hGK : ∀ i, ‖Gcoord4 i - K4 i‖ ≤
      (11 / 15 : ℝ) * b i ^ 2 * D6)
    (hGG : ∀ i, ‖Gcoord4 i - G4‖ ≤
      ((∑ j, b j ^ 4) / 12 : ℝ) * D8) :
    ‖G0 - R0 - ((∑ i, b i ^ 4) / 12 : ℝ) • G4‖ ≤
      (∑ i, b i ^ 4) ^ 2 / 144 * D8 +
        11 * (∑ i, b i ^ 6) / 180 * D6 := by
  classical
  have hcorr : ((∑ i, b i ^ 4) / 12 : ℝ) • G4 =
      ∑ i, (b i ^ 4 / 12 : ℝ) • G4 := by
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.sum_div]
  rw [hfirst, hcorr, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    ‖∑ i, (b i ^ 4 / 12 : ℝ) • (K4 i - G4)‖ ≤
        ∑ i, ‖(b i ^ 4 / 12 : ℝ) • (K4 i - G4)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((11 / 180 : ℝ) * b i ^ 6 * D6 +
        (b i ^ 4 * (∑ j, b j ^ 4) / 144) * D8) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (by positivity) (by norm_num))]
      have hsplit : ‖K4 i - G4‖ ≤
          ‖Gcoord4 i - K4 i‖ + ‖Gcoord4 i - G4‖ := by
        calc
          ‖K4 i - G4‖ =
              ‖-(Gcoord4 i - K4 i) + (Gcoord4 i - G4)‖ := by
                congr 1
                ring
          _ ≤ _ := by
            have h := norm_add_le (-(Gcoord4 i - K4 i))
              (Gcoord4 i - G4)
            simpa only [norm_neg] using h
      calc
        b i ^ 4 / 12 * ‖K4 i - G4‖ ≤
            b i ^ 4 / 12 *
              (‖Gcoord4 i - K4 i‖ + ‖Gcoord4 i - G4‖) :=
          mul_le_mul_of_nonneg_left hsplit
            (div_nonneg (by positivity) (by norm_num))
        _ ≤ b i ^ 4 / 12 *
            ((11 / 15 : ℝ) * b i ^ 2 * D6 +
              ((∑ j, b j ^ 4) / 12 : ℝ) * D8) := by
          gcongr
          · exact hGK i
          · exact hGG i
        _ = (11 / 180 : ℝ) * b i ^ 6 * D6 +
            (b i ^ 4 * (∑ j, b j ^ 4) / 144) * D8 := by ring
    _ = (∑ i, b i ^ 4) ^ 2 / 144 * D8 +
          11 * (∑ i, b i ^ 6) / 180 * D6 := by
      rw [Finset.sum_add_distrib]
      have hsum6 : (∑ i, (11 / 180 : ℝ) * b i ^ 6 * D6) =
          11 * (∑ i, b i ^ 6) / 180 * D6 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      have hsum8 : (∑ i, (b i ^ 4 * (∑ j, b j ^ 4) / 144) * D8) =
          (∑ i, b i ^ 4) ^ 2 / 144 * D8 := by
        simp_rw [show ∀ i, (b i ^ 4 * (∑ j, b j ^ 4) / 144) * D8 =
          ((b i ^ 4 * (∑ j, b j ^ 4)) * (1 / 144)) * D8 by
            intro i; ring]
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
        ring
      rw [hsum6, hsum8]
      ring

end CertifiedJL
