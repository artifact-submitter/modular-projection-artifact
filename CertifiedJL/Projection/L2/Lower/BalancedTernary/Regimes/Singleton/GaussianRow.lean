/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Singleton.Gaussian
import CertifiedJL.Projection.L2.Lower.BalancedTernary.ThresholdLower
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Intermediate.PMF

/-!
# Singleton Gaussian bounds for affine sparse rows

The exact balanced-ternary marginal turns a retained singleton into the
average of the wrapped kernel at zero and at its coefficient. Positive-Fourier
transport then bounds the full affine row, uniformly over its fixed shift.
-/

open MeasureTheory

namespace CertifiedJL

/-- A retained singleton has the exact balanced-ternary wrapped expectation.
This identity imposes no sign condition on the retained coefficient. -/
theorem sparseRow_wrappedGaussianKernel_singleton_eq
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (s : ℝ) :
    (∫ row, wrappedGaussianKernel q s
        (∑ j, row j * (if j ∈ ({i} : Finset (Fin d)) then w j else 0))
        ∂(sparseRademacherRow d).toMeasure) =
      (wrappedGaussianKernel q s 0 + wrappedGaussianKernel q s (w i)) / 2 := by
  classical
  simp only [Finset.mem_singleton, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← integral_map_of_stronglyMeasurable
    (μ := (sparseRademacherRow d).toMeasure)
    (φ := fun row : Fin d → ℤ => row i)
    (f := fun z : ℤ => wrappedGaussianKernel q s (z * w i))
    (measurable_pi_apply i)
    (measurable_of_countable
      (fun z : ℤ => wrappedGaussianKernel q s (z * w i))).stronglyMeasurable]
  rw [PMF.toMeasure_map _ _ (measurable_pi_apply i), sparseRademacherRow_marginal]
  rw [sparseEntry_integral_eq_mix]
  simp only [neg_one_mul, zero_mul, one_mul, wrappedGaussianKernel_neg]
  ring

/-- The wrapped transform of a retained large coordinate satisfies the sharper
singleton envelope. No modulus parity or input-norm hypothesis is needed. -/
theorem sparseRow_wrappedGaussianKernel_singleton_le_envelope
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) {B t : ℝ}
    (hB : 0 < B) (hmargin : 3 * B ≤ (q : ℝ))
    (hlarge : (49 / 50 : ℝ) * B ≤ |(w i : ℝ)|)
    (hcentered : 2 * |(w i : ℝ)| ≤ (q : ℝ))
    (ht : (1250 / 2401 : ℝ) ≤ t) :
    (∫ row, wrappedGaussianKernel q (t / B ^ 2)
        (∑ j, row j * (if j ∈ ({i} : Finset (Fin d)) then w j else 0))
        ∂(sparseRademacherRow d).toMeasure) ≤ singletonGaussianEnvelope t := by
  rw [sparseRow_wrappedGaussianKernel_singleton_eq]
  exact wrappedGaussianKernel_singleton_le_envelope (w i) hB hmargin hlarge hcentered ht

/-- A single sufficiently large centered coordinate bounds the full affine
row transform. The shift and selected coordinate are fixed before sampling
the row; all other coefficients are unrestricted. -/
theorem sparseRow_affineCenteredGaussian_le_singletonGaussianEnvelope
    {q d : ℕ} (shift : ℤ) (w : Fin d → ℤ) (i : Fin d) {B t : ℝ}
    (hq : Odd q) (hB : 0 < B) (hmargin : 3 * B ≤ (q : ℝ))
    (hlarge : (49 / 50 : ℝ) * B ≤ |(w i : ℝ)|)
    (hcentered : 2 * |(w i : ℝ)| ≤ (q : ℝ))
    (ht : (1250 / 2401 : ℝ) ≤ t) :
    (∫ row, Real.exp (-(t / B ^ 2) * affineSparseLowerRowKernel q shift w row)
        ∂(sparseRademacherRow d).toMeasure) ≤ singletonGaussianEnvelope t := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  exact (sparseRow_affineCenteredGaussian_le_wrappedGaussianKernel_restrict
    shift w {i} hq (div_pos htpos (sq_pos_of_pos hB))).trans
      (sparseRow_wrappedGaussianKernel_singleton_le_envelope
        w i hB hmargin hlarge hcentered ht)

/-- Protocol-input specialization with a natural public threshold and a
centered input. The selected large coefficient is the only norm information
used by this branch. -/
theorem sparseRow_affineCenteredGaussian_le_singletonGaussianEnvelope_of_centeredInput
    {q d b : ℕ} (shift : ℤ) (w : Fin d → ℤ) (i : Fin d) {t : ℝ}
    (hq : Odd q) (hb : 0 < b) (hmargin : 3 * b ≤ q)
    (hcentered : CenteredInput q w) (hlarge : 49 * b ≤ 50 * (w i).natAbs)
    (ht : (1250 / 2401 : ℝ) ≤ t) :
    (∫ row, Real.exp (-(t / (b : ℝ) ^ 2) * affineSparseLowerRowKernel q shift w row)
        ∂(sparseRademacherRow d).toMeasure) ≤ singletonGaussianEnvelope t := by
  have habs : |w i| ≤ ((q / 2 : ℕ) : ℤ) := (abs_le).2 (hcentered i)
  have hnat : (w i).natAbs ≤ q / 2 := by
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  have htwice : 2 * (w i).natAbs ≤ q :=
    (Nat.mul_le_mul_left 2 hnat).trans (Nat.mul_div_le q 2)
  have habsReal : |(w i : ℝ)| = ((w i).natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  apply sparseRow_affineCenteredGaussian_le_singletonGaussianEnvelope
    shift w i hq (by exact_mod_cast hb) (by exact_mod_cast hmargin)
  · rw [habsReal]
    have hlargeReal : (49 : ℝ) * b ≤ 50 * ((w i).natAbs : ℝ) := by
      exact_mod_cast hlarge
    linarith
  · rw [habsReal]
    exact_mod_cast htwice
  · exact ht

end CertifiedJL
