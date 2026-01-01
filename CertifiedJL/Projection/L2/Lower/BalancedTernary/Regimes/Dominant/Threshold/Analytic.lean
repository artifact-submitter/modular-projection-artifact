/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Cell
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Fourier

/-!
# Explicit-modulus dominant row bounds

The cap-relative row cells tie their modular-image endpoint to the residual
endpoint.  Public-threshold geometry supplies a separate lower bound for
`q / A`; this module keeps that parameter independent.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL

private theorem exp_neg_div_one_sub_exp_neg_mono_threshold
    {a₀ a c₀ c : ℝ} (haa : a₀ ≤ a)
    (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) :
    Real.exp (-a) / (1 - Real.exp (-c)) ≤
      Real.exp (-a₀) / (1 - Real.exp (-c₀)) := by
  have hnum : Real.exp (-a) ≤ Real.exp (-a₀) :=
    Real.exp_le_exp.mpr (neg_le_neg haa)
  have hc : 0 < c := hc₀.trans_le hcc
  have hden₀ : 0 < 1 - Real.exp (-c₀) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc₀))
  have hden : 0 < 1 - Real.exp (-c) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hden_order : 1 - Real.exp (-c₀) ≤ 1 - Real.exp (-c) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hcc)
    linarith
  exact div_le_div₀ (Real.exp_nonneg _) hnum hden₀ hden_order

/-- The active modular-image envelope is monotone in its independent lower
modulus endpoint. -/
theorem shiftedActiveWrap_le_thresholdCell
    (lower upper modulusLower z : ℚ) (u B : ℝ)
    (hu : 0 < u) (hu_upper : u ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ))
    (hmodulusLower : 1 < (modulusLower : ℝ))
    (hB : (modulusLower : ℝ) ≤ B) :
    let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * u)
    Real.exp (-alpha * (B - 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
      Real.exp (-alpha * (B + 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B))) ≤
      thresholdDominantCellActiveWrap lower upper modulusLower z := by
  dsimp only
  let B₀ : ℝ := modulusLower
  let alpha₀ : ℝ := (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * u)
  have hupper : 0 < (upper : ℝ) := hu.trans_le hu_upper
  have hden : 0 < 1 + (z : ℝ) * u := by positivity
  have hden₀ : 0 < 1 + (z : ℝ) * (upper : ℝ) := by positivity
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have halpha₀ : 0 < alpha₀ := by dsimp [alpha₀]; positivity
  have halpha_le : alpha₀ ≤ alpha := by
    have hden_le : 1 + (z : ℝ) * u ≤
        1 + (z : ℝ) * (upper : ℝ) := by
      simpa [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hu_upper hz.le) 1
    apply (div_le_div_iff₀ hden₀ hden).2
    exact mul_le_mul_of_nonneg_left hden_le hz.le
  have hB₀ : 1 < B₀ := by simpa [B₀] using hmodulusLower
  have hB1 : 1 < B := hB₀.trans_le (by simpa [B₀] using hB)
  have hminus_sq : (B₀ - 1) ^ 2 ≤ (B - 1) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by linarith)).2 (by simpa [B₀] using hB)
  have hplus_sq : (B₀ + 1) ^ 2 ≤ (B + 1) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by linarith)).2 (by simpa [B₀] using hB)
  have hminus_rate : 3 * B₀ ^ 2 - 2 * B₀ ≤ 3 * B ^ 2 - 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) - 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by simpa [B₀] using hB
    nlinarith [mul_nonneg hdiff hsum]
  have hplus_rate : 3 * B₀ ^ 2 + 2 * B₀ ≤ 3 * B ^ 2 + 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) + 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by simpa [B₀] using hB
    nlinarith [mul_nonneg hdiff hsum]
  have hminus_rate_pos : 0 < 3 * B₀ ^ 2 - 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ - 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hplus_rate_pos : 0 < 3 * B₀ ^ 2 + 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ + 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hminus := exp_neg_div_one_sub_exp_neg_mono_threshold
    (mul_le_mul halpha_le hminus_sq (sq_nonneg _) halpha.le)
    (mul_pos halpha₀ hminus_rate_pos)
    (mul_le_mul halpha_le hminus_rate (by positivity) halpha.le)
  have hplus := exp_neg_div_one_sub_exp_neg_mono_threshold
    (mul_le_mul halpha_le hplus_sq (sq_nonneg _) halpha.le)
    (mul_pos halpha₀ hplus_rate_pos)
    (mul_le_mul halpha_le hplus_rate (by positivity) halpha.le)
  unfold thresholdDominantCellActiveWrap
  dsimp [B₀, alpha₀, alpha] at *
  simpa only [neg_mul] using add_le_add hminus hplus

/-- The reindexed active conditional row satisfies the explicit-modulus cell
bound. -/
theorem dominantRemainderFin_active_le_thresholdCellRow
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ)
    (lower upper modulusLower z : ℚ)
    (hq : Odd q) (hi : w i ≠ 0)
    (hlower : 0 ≤ (lower : ℝ))
    (hu_actual : 0 < dominantResidualRatio w i)
    (hlower_u : (lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ))
    (hmodulusLower : 1 < (modulusLower : ℝ))
    (hmodulus : (modulusLower : ℝ) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    (∫ row, Real.exp
          (-(z : ℝ) * ((centeredMod q
            ((dominantAmplitude w i : ℤ) +
              ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
                (dominantAmplitude w i : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      thresholdDominantCellActiveRow lower upper modulusLower z := by
  let A : ℕ := dominantAmplitude w i
  let V : ℝ := dominantRemainderSqNorm w i
  let u : ℝ := dominantResidualRatio w i
  let B : ℝ := (q : ℝ) / (A : ℝ)
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * u)
  let rho : ℝ :=
    let s := (z : ℝ) * u
    let h := (z : ℝ) * Real.sqrt u / (1 + s)
    min 1 (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
      3 * s ^ 2 + 4 * s ^ 2 * h ^ 4)
  let central : ℝ := Real.exp (-(z : ℝ) / (1 + (z : ℝ) * u)) * rho
  let wrap : ℝ :=
    Real.exp (-alpha * (B - 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
      Real.exp (-alpha * (B + 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))
  have hA : 0 < A := by dsimp [A]; exact dominantAmplitude_pos hi
  have hu : 0 < u := hu_actual
  have hV : 0 < V := by
    dsimp [V, u, dominantResidualRatio] at hu ⊢
    rcases div_pos_iff.mp hu with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (by positivity)) h.1)
  have hnorm : ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 = V := by
    dsimp [V]
    rw [← realCast_sqNorm, sqNorm_dominantRemainderFinWeights]
  have hmass :
      ∑ j, ((dominantRemainderFinWeights w i j : ℝ) / (A : ℝ)) ^ 2 = u := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, hnorm]
    rfl
  have hB1 : 1 < B := by
    dsimp [B, A]
    exact hmodulusLower.trans_le hmodulus
  have hperiod := sparseRow_shiftedNormalizedPeriodization_nonzeroImageBound
    (dominantRemainderFinWeights w i) q A V (z : ℝ)
    hq hA hV hnorm hz hB1
  have hcore := sparseRow_shiftedDominantRow
    (fun j => (dominantRemainderFinWeights w i j : ℝ) / (A : ℝ))
    u (z : ℝ) hu hz hmass
  have hdot (row : Fin (Fintype.card (DominantRemainderIndex i)) → ℤ) :
      realRowDot row
          (fun j => (dominantRemainderFinWeights w i j : ℝ) / (A : ℝ)) =
        ((∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
          (A : ℝ) := by
    simp only [realRowDot, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcentral :
      (∫ row, Real.exp (-(z : ℝ) * ((((A : ℤ) +
          ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
            (A : ℝ)) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤ central := by
    rw [show (∫ row, Real.exp (-(z : ℝ) * ((((A : ℤ) +
        ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
          (A : ℝ)) ^ 2)
      ∂(sparseRademacherRow (Fintype.card (DominantRemainderIndex i))).toMeasure) =
      ∫ row, Real.exp (-(z : ℝ) * (1 + realRowDot row
        (fun j => (dominantRemainderFinWeights w i j : ℝ) / (A : ℝ))) ^ 2)
      ∂(sparseRademacherRow (Fintype.card (DominantRemainderIndex i))).toMeasure by
        apply integral_congr_ae
        filter_upwards [] with row
        congr 1
        rw [hdot]
        push_cast
        field_simp [show (A : ℝ) ≠ 0 by exact_mod_cast hA.ne']]
    simpa only [central, rho] using hcore
  have hrho : rho ≤ dominantCellRho lower upper z := by
    by_cases hlower_zero : lower = 0
    · subst lower
      have hcell : dominantCellRho 0 upper z = 1 := by
        unfold dominantCellRho dominantCellHsq
        simp only [Rat.cast_zero, mul_zero, zero_div, zero_mul, sub_zero]
        rw [min_eq_left]
        nlinarith [sq_nonneg ((z : ℝ) * (upper : ℝ)),
          sq_nonneg
            (max 0 (max
              ((z : ℝ) ^ 2 * (upper : ℝ) /
                (1 + (z : ℝ) * (upper : ℝ)) ^ 2)
              (if 1 ≤ z * upper then (z : ℝ) / 4 else 0)))]
      rw [hcell]
      dsimp [rho]
      exact min_le_left _ _
    · have hlower_pos : 0 < (lower : ℝ) := by
        have hne : (lower : ℝ) ≠ 0 := by exact_mod_cast hlower_zero
        exact lt_of_le_of_ne hlower (Ne.symm hne)
      exact shiftedDominantRho_le_cell
        lower upper z u hlower_pos hlower_u hu_upper hz
  have hcentral_nonneg : 0 ≤ central :=
    (integral_nonneg fun _ => Real.exp_nonneg _).trans hcentral
  have hrho_nonneg : 0 ≤ rho := by
    dsimp [central] at hcentral_nonneg
    by_contra hneg
    have hrho_neg : rho < 0 := lt_of_not_ge hneg
    exact (not_lt_of_ge hcentral_nonneg)
      (mul_neg_of_pos_of_neg (Real.exp_pos _) hrho_neg)
  have hden_le : 1 + (z : ℝ) * u ≤
      1 + (z : ℝ) * (upper : ℝ) := by
    simpa [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hu_upper hz.le) 1
  have hexp : Real.exp (-(z : ℝ) / (1 + (z : ℝ) * u)) ≤
      Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hdenu : 0 < 1 + (z : ℝ) * u := by positivity
    have hupper : 0 < (upper : ℝ) := hu.trans_le hu_upper
    have hdenUpper : 0 < 1 + (z : ℝ) * (upper : ℝ) := by positivity
    have hdiv := (div_le_div_iff₀ hdenUpper hdenu).2
      (mul_le_mul_of_nonneg_left hden_le hz.le)
    simpa only [neg_div] using neg_le_neg hdiv
  have hcentral_cell : central ≤
      Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
        dominantCellRho lower upper z := by
    dsimp [central]
    calc
      _ ≤ Real.exp (-(z : ℝ) / (1 + (z : ℝ) * u)) *
          dominantCellRho lower upper z :=
        mul_le_mul_of_nonneg_left hrho (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (hrho_nonneg.trans hrho)
  have hwrap_cell :
      wrap ≤ thresholdDominantCellActiveWrap lower upper modulusLower z := by
    simpa only [wrap, alpha, B, A, u] using
      shiftedActiveWrap_le_thresholdCell lower upper modulusLower z u B
        hu hu_upper hz hmodulusLower
          (by simpa [B, A] using hmodulus)
  have hcell_central_nonneg : 0 ≤
      Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
        dominantCellRho lower upper z :=
    mul_nonneg (Real.exp_nonneg _) (hrho_nonneg.trans hrho)
  have hcell_wrap_nonneg :
      0 ≤ thresholdDominantCellActiveWrap lower upper modulusLower z := by
    have hwrap_nonneg : 0 ≤ wrap := by
      have halpha : 0 < alpha := by dsimp [alpha]; positivity
      have hminus : 0 < alpha * (3 * B ^ 2 - 2 * B) := by
        have : 0 < B * (3 * B - 2) := mul_pos (by linarith) (by linarith)
        have : 0 < 3 * B ^ 2 - 2 * B := by nlinarith
        positivity
      have hplus : 0 < alpha * (3 * B ^ 2 + 2 * B) := by
        have : 0 < B * (3 * B + 2) := mul_pos (by linarith) (by linarith)
        have : 0 < 3 * B ^ 2 + 2 * B := by nlinarith
        positivity
      dsimp [wrap]
      have hdminus : 0 < 1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B)) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      have hdplus : 0 < 1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      positivity
    exact hwrap_nonneg.trans hwrap_cell
  have hENN : ENNReal.ofReal
        (∫ row, Real.exp
          (-(z : ℝ) * ((centeredMod q
            ((dominantAmplitude w i : ℤ) +
              ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
                (dominantAmplitude w i : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      ENNReal.ofReal
        (thresholdDominantCellActiveRow lower upper modulusLower z) := by
    calc
      _ ≤ ENNReal.ofReal central + ENNReal.ofReal wrap := by
        simpa only [A, V, u, B, alpha, central, wrap,
          dominantResidualRatio] using hperiod.trans
          (add_le_add (ENNReal.ofReal_mono hcentral) le_rfl)
      _ ≤ ENNReal.ofReal
          (Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
            dominantCellRho lower upper z) +
          ENNReal.ofReal
            (thresholdDominantCellActiveWrap lower upper modulusLower z) := by
        exact add_le_add (ENNReal.ofReal_mono hcentral_cell)
          (ENNReal.ofReal_mono hwrap_cell)
      _ = ENNReal.ofReal
          (thresholdDominantCellActiveRow lower upper modulusLower z) := by
        rw [← ENNReal.ofReal_add hcell_central_nonneg hcell_wrap_nonneg]
        rfl
  have hintegral_nonneg : 0 ≤ ∫ row, Real.exp
      (-(z : ℝ) * ((centeredMod q
        ((dominantAmplitude w i : ℤ) +
          ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
            (dominantAmplitude w i : ℝ)) ^ 2)
      ∂(sparseRademacherRow
        (Fintype.card (DominantRemainderIndex i))).toMeasure :=
    integral_nonneg fun _ => Real.exp_nonneg _
  have hactive_nonneg :
      0 ≤ thresholdDominantCellActiveRow lower upper modulusLower z := by
    unfold thresholdDominantCellActiveRow
    exact add_nonneg hcell_central_nonneg hcell_wrap_nonneg
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  rw [ENNReal.toReal_ofReal hintegral_nonneg,
    ENNReal.toReal_ofReal hactive_nonneg] at hreal
  exact hreal

/-- The reindexed inactive conditional row satisfies the independent-modulus
cell bound. -/
theorem dominantRemainderFin_inactive_le_thresholdCellRow
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ)
    (lower upper modulusLower z : ℚ)
    (hq : Odd q) (hi : w i ≠ 0)
    (hlower : 0 ≤ (lower : ℝ))
    (hu_actual : 0 < dominantResidualRatio w i)
    (hlower_u : (lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ))
    (hmodulusLower : 1 < (modulusLower : ℝ))
    (hmodulus : (modulusLower : ℝ) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    ∫ row, Real.exp
        (-(z : ℝ) * dominantResidualRatio w i *
          ((centeredMod q
            (∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure ≤
      thresholdDominantCellInactiveRow lower upper modulusLower z := by
  let u : ℝ := dominantResidualRatio w i
  let s : ℝ := (z : ℝ) * u
  let sLower : ℝ := (z : ℝ) * (lower : ℝ)
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  let central : ℝ :=
    (1 / Real.sqrt (1 + sLower)) *
      (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + sUpper)) /
        (1 - (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3))
  let wrap : ℝ :=
    thresholdDominantCellInactiveWrap lower upper modulusLower z
  have hA : 0 < (dominantAmplitude w i : ℝ) := by
    exact_mod_cast dominantAmplitude_pos hi
  have hu_pos : 0 < u := hu_actual
  have hU : 0 < dominantRemainderSqNorm w i := by
    have hUreal : 0 < (dominantRemainderSqNorm w i : ℝ) := by
      dsimp [u, dominantResidualRatio] at hu_pos
      rcases (div_pos_iff.mp hu_pos) with h | h
      · exact h.1
      · exact False.elim ((not_lt_of_ge (by positivity)) h.1)
    exact_mod_cast hUreal
  have hs : 0 < s := by dsimp [s]; positivity
  have hsLower : 0 ≤ sLower := by dsimp [sLower]; positivity
  have hsLower_le : sLower ≤ s := by
    dsimp [sLower, s]
    exact mul_le_mul_of_nonneg_left hlower_u hz.le
  have hsUpper : s ≤ sUpper := by
    dsimp [sUpper, s]
    exact mul_le_mul_of_nonneg_left hu_upper hz.le
  let a : Fin (Fintype.card (DominantRemainderIndex i)) → ℝ :=
    fun j => (dominantRemainderFinWeights w i j : ℝ) /
      Real.sqrt (dominantRemainderSqNorm w i : ℝ)
  let S := Finset.univ.filter fun j => a j ≠ 0
  have hS : ∀ j, j ∈ S ↔ a j ≠ 0 := by intro j; simp [S]
  have hUreal : 0 < (dominantRemainderSqNorm w i : ℝ) := by
    exact_mod_cast hU
  have hsqrtU : Real.sqrt (dominantRemainderSqNorm w i : ℝ) ^ 2 =
      (dominantRemainderSqNorm w i : ℝ) := Real.sq_sqrt hUreal.le
  have hnorm :
      ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 =
        (dominantRemainderSqNorm w i : ℝ) := by
    rw [← realCast_sqNorm, sqNorm_dominantRemainderFinWeights]
  have ha : ∑ j, a j ^ 2 = 1 := by
    calc
      ∑ j, a j ^ 2 =
          ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 /
            (dominantRemainderSqNorm w i : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [a]
        rw [div_pow, hsqrtU]
      _ = (∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2) /
          (dominantRemainderSqNorm w i : ℝ) := by rw [Finset.sum_div]
      _ = 1 := by rw [hnorm, div_self hUreal.ne']
  have hproduct :
      ∏ j ∈ S, gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2) ≤
        ENNReal.ofReal central := by
    simpa [central] using gaussianCosineProduct_le_dominantCentral
      a S hS ha hsLower hsLower_le hs hsUpper
  have hperiod := dominantRemainderFin_modular_le_scalarProduct_add_wrap
    w i q s hq hU hs
  have hc₀ : 0 <
      ((z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
        (modulusLower : ℝ) ^ 2 := by
    have hden : 0 < 1 + (z : ℝ) * (upper : ℝ) := by
      have hu_nonneg : 0 ≤ (upper : ℝ) :=
        (hlower.trans hlower_u).trans hu_upper
      positivity
    positivity
  have hc_compare :
      ((z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
          (modulusLower : ℝ) ^ 2 ≤
        s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s) := by
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hden_u : 0 < 1 + (z : ℝ) * u := by positivity
    have hupper_nonneg : 0 ≤ (upper : ℝ) :=
      (hlower.trans hlower_u).trans hu_upper
    have hden_upper : 0 < 1 + (z : ℝ) * (upper : ℝ) := by positivity
    have halpha :
        (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ)) ≤
          (z : ℝ) / (1 + (z : ℝ) * u) := by
      exact div_le_div_of_nonneg_left hz.le hden_u
        (by nlinarith [mul_le_mul_of_nonneg_left hu_upper hz.le])
    have hmod_sq : (modulusLower : ℝ) ^ 2 ≤
          ((q : ℝ) / (dominantAmplitude w i : ℝ)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hmodulus
    have hboth := mul_le_mul halpha hmod_sq (sq_nonneg _)
      (by positivity : 0 ≤ (z : ℝ) / (1 + (z : ℝ) * u))
    calc
      _ ≤ ((z : ℝ) / (1 + (z : ℝ) * u)) *
          ((q : ℝ) / (dominantAmplitude w i : ℝ)) ^ 2 := hboth
      _ = s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s) := by
        dsimp [s, u, dominantResidualRatio]
        field_simp [hA.ne', hUreal.ne', (Real.sqrt_pos.2 hUreal).ne', hsqrtU]
        rw [hsqrtU]
        ring
  have hwrapReal :
      2 * Real.exp
          (-s * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                (1 + s))) ^ 3) ≤ wrap := by
    have hmono := twoSidedGeometricTail_antitone hc₀ hc_compare
    have hpoweq :
        (Real.exp (-((z : ℝ) / (1 + (z : ℝ) * (upper : ℝ)) *
          (modulusLower : ℝ) ^ 2))) ^ 3 =
        Real.exp (-3 * ((z : ℝ) /
          (1 + (z : ℝ) * (upper : ℝ))) *
            (modulusLower : ℝ) ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp [wrap, thresholdDominantCellInactiveWrap]
    rw [← hpoweq]
    convert hmono using 1 <;> ring
  have hcentral_nonneg : 0 ≤ central := by
    dsimp [central]
    have hsUpper_pos : 0 < 1 + sUpper := by linarith
    have htheta : Real.exp (-Real.pi ^ 2 / (1 + sUpper)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos Real.pi_pos))
        hsUpper_pos
    have hpow := pow_lt_pow_left₀ htheta
      (Real.exp_pos (-Real.pi ^ 2 / (1 + sUpper))).le
      (by norm_num : (3 : ℕ) ≠ 0)
    have hden : 0 < 1 -
        (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3 :=
      sub_pos.mpr (by simpa using hpow)
    positivity
  have hwrap_nonneg : 0 ≤ wrap := by
    have hactual_nonneg : 0 ≤
        2 * Real.exp
          (-s * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                (1 + s))) ^ 3) := by
      have hrate : 0 < s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s) := by
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq.pos
        positivity
      have hexp : Real.exp (-s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
            (1 + s)) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        convert neg_lt_zero.mpr hrate using 1 <;> ring
      have hpow := pow_lt_pow_left₀ hexp (Real.exp_pos _).le
        (by norm_num : (3 : ℕ) ≠ 0)
      have hden : 0 < 1 - (Real.exp
          (-s * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
              (1 + s))) ^ 3 := sub_pos.mpr (by simpa using hpow)
      exact div_nonneg (by positivity) hden.le
    exact hactual_nonneg.trans hwrapReal
  have hENN : ENNReal.ofReal
      (∫ row, Real.exp
        (-s * ((centeredMod q
          (∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      ENNReal.ofReal (central + wrap) := by
    calc
      _ ≤ (∏ j ∈ S,
          gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2)) +
          ENNReal.ofReal
            (2 * Real.exp
              (-s * ((q : ℝ) /
                Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
              (1 - (Real.exp
                (-s * ((q : ℝ) /
                  Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                    (1 + s))) ^ 3)) := by
        simpa [a, S] using hperiod
      _ ≤ ENNReal.ofReal central + ENNReal.ofReal wrap :=
        add_le_add hproduct (ENNReal.ofReal_mono hwrapReal)
      _ = ENNReal.ofReal (central + wrap) := by
        rw [ENNReal.ofReal_add hcentral_nonneg hwrap_nonneg]
  have hreal := ENNReal.toReal_le_of_le_ofReal
    (add_nonneg hcentral_nonneg hwrap_nonneg) hENN
  rw [ENNReal.toReal_ofReal] at hreal
  · simpa [u, s, central, wrap, sLower, sUpper,
      thresholdDominantCellInactiveRow] using hreal
  · exact integral_nonneg fun _ => Real.exp_nonneg _

/-- The exact active conditional row kernel satisfies an explicit-modulus
public-threshold cell bound. -/
theorem dominantActiveRowKernel_le_thresholdCell
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ)
    (lower upper modulusLower z : ℚ)
    (hq : Odd q) (hi : w i ≠ 0)
    (hlower : 0 ≤ (lower : ℝ))
    (hu_actual : 0 < dominantResidualRatio w i)
    (hlower_u : (lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (upper : ℝ))
    (hz : 0 ≤ (z : ℝ))
    (hmodulusLower : 1 < (modulusLower : ℝ))
    (hmodulus : (modulusLower : ℝ) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    ∫ x, Real.exp (-(z : ℝ) * dominantNormalizedRowKernel q w i x)
        ∂(dominantConditionalRowPMF i true).toMeasure ≤
      thresholdDominantCellActiveRow lower upper modulusLower z := by
  by_cases hz₀ : (z : ℝ) = 0
  · have hzRat : z = 0 := by exact_mod_cast hz₀
    subst z
    simp [thresholdDominantCellActiveRow,
      thresholdDominantCellActiveWrap, dominantCellRho, dominantCellHsq]
  have hzpos : 0 < (z : ℝ) := lt_of_le_of_ne hz (Ne.symm hz₀)
  let A : ℝ := dominantAmplitude w i
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast dominantAmplitude_pos hi
  have hreindex := dominantConditionalRow_integral_eq_shiftedRemainder
    w i true ((z : ℝ) / A ^ 2) hq
  have hscalar := dominantRemainderFin_active_le_thresholdCellRow
    w i q lower upper modulusLower z hq hi hlower hu_actual
      hlower_u hu_upper hzpos
      hmodulusLower hmodulus
  calc
    ∫ x, Real.exp (-(z : ℝ) * dominantNormalizedRowKernel q w i x)
        ∂(dominantConditionalRowPMF i true).toMeasure =
      ∫ x, Real.exp (-((z : ℝ) / A ^ 2) *
          (centeredMod q (∑ j, x j * w j) : ℝ) ^ 2)
        ∂(dominantConditionalRowPMF i true).toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [dominantNormalizedRowKernel, A]
          congr 1
          field_simp [hA.ne']
    _ = ∫ row, Real.exp (-((z : ℝ) / A ^ 2) *
          (centeredMod q
            ((dominantAmplitude w i : ℤ) +
              ∑ j, row j * dominantRemainderFinWeights w i j) : ℝ) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure := by
            simpa [A] using hreindex
    _ ≤ thresholdDominantCellActiveRow lower upper modulusLower z := by
      convert hscalar using 1
      apply integral_congr_ae
      filter_upwards [] with row
      congr 1
      rw [div_pow]
      ring

/-- The exact inactive conditional row kernel satisfies an explicit-modulus
public-threshold cell bound. -/
theorem dominantInactiveRowKernel_le_thresholdCell
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ)
    (lower upper modulusLower z : ℚ)
    (hq : Odd q) (hi : w i ≠ 0)
    (hlower : 0 ≤ (lower : ℝ))
    (hu_actual : 0 < dominantResidualRatio w i)
    (hlower_u : (lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (upper : ℝ))
    (hz : 0 ≤ (z : ℝ))
    (hmodulusLower : 1 < (modulusLower : ℝ))
    (hmodulus : (modulusLower : ℝ) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    ∫ x, Real.exp (-(z : ℝ) * dominantNormalizedRowKernel q w i x)
        ∂(dominantConditionalRowPMF i false).toMeasure ≤
      thresholdDominantCellInactiveRow lower upper modulusLower z := by
  by_cases hz₀ : (z : ℝ) = 0
  · have hzRat : z = 0 := by exact_mod_cast hz₀
    subst z
    have htheta : Real.exp (-Real.pi ^ 2) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [sq_pos_of_pos Real.pi_pos]
    have hpow := pow_lt_pow_left₀ htheta (Real.exp_pos _).le
      (by norm_num : (3 : ℕ) ≠ 0)
    have htail : 0 ≤ 2 * Real.exp (-Real.pi ^ 2) /
        (1 - (Real.exp (-Real.pi ^ 2)) ^ 3) := by
      have hden : 0 < 1 - (Real.exp (-Real.pi ^ 2)) ^ 3 :=
        sub_pos.mpr (by simpa using hpow)
      positivity
    simp [thresholdDominantCellInactiveRow,
      thresholdDominantCellInactiveWrap, htail]
  have hzpos : 0 < (z : ℝ) := lt_of_le_of_ne hz (Ne.symm hz₀)
  let A : ℝ := dominantAmplitude w i
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast dominantAmplitude_pos hi
  have hreindex := dominantConditionalRow_integral_eq_shiftedRemainder
    w i false ((z : ℝ) / A ^ 2) hq
  have hscalar := dominantRemainderFin_inactive_le_thresholdCellRow
    w i q lower upper modulusLower z hq hi hlower hu_actual
      hlower_u hu_upper hzpos
      hmodulusLower hmodulus
  have hU : 0 < (dominantRemainderSqNorm w i : ℝ) := by
    have hupos : 0 < dominantResidualRatio w i := hu_actual
    dsimp [dominantResidualRatio] at hupos
    rcases (div_pos_iff.mp hupos) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (by positivity)) h.1)
  calc
    ∫ x, Real.exp (-(z : ℝ) * dominantNormalizedRowKernel q w i x)
        ∂(dominantConditionalRowPMF i false).toMeasure =
      ∫ x, Real.exp (-((z : ℝ) / A ^ 2) *
          (centeredMod q (∑ j, x j * w j) : ℝ) ^ 2)
        ∂(dominantConditionalRowPMF i false).toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [dominantNormalizedRowKernel, A]
          congr 1
          field_simp [hA.ne']
    _ = ∫ row, Real.exp (-((z : ℝ) / A ^ 2) *
          (centeredMod q
            (0 + ∑ j, row j * dominantRemainderFinWeights w i j) : ℝ) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure := by
            simpa [A] using hreindex
    _ ≤ thresholdDominantCellInactiveRow lower upper modulusLower z := by
      convert hscalar using 1
      apply integral_congr_ae
      filter_upwards [] with row
      simp only [zero_add]
      congr 1
      dsimp [dominantResidualRatio, A]
      rw [div_pow, Real.sq_sqrt hU.le]
      field_simp [hA.ne', hU.ne']

/-- Both activity states obey the same explicit-modulus cell interface. -/
theorem dominantRowKernel_le_thresholdCell
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ)
    (lower upper modulusLower z : ℚ) (activity : Bool)
    (hq : Odd q) (hi : w i ≠ 0)
    (hlower : 0 ≤ (lower : ℝ))
    (hu_actual : 0 < dominantResidualRatio w i)
    (hlower_u : (lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (upper : ℝ))
    (hz : 0 ≤ (z : ℝ))
    (hmodulusLower : 1 < (modulusLower : ℝ))
    (hmodulus : (modulusLower : ℝ) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    ∫ x, Real.exp (-(z : ℝ) * dominantNormalizedRowKernel q w i x)
        ∂(dominantConditionalRowPMF i activity).toMeasure ≤
      if activity then
        thresholdDominantCellActiveRow lower upper modulusLower z
      else thresholdDominantCellInactiveRow lower upper modulusLower z := by
  cases activity
  · simpa using dominantInactiveRowKernel_le_thresholdCell
      w i q lower upper modulusLower z hq hi hlower hu_actual
        hlower_u hu_upper hz
        hmodulusLower hmodulus
  · simpa using dominantActiveRowKernel_le_thresholdCell
      w i q lower upper modulusLower z hq hi hlower hu_actual
        hlower_u hu_upper hz
        hmodulusLower hmodulus

set_option maxHeartbeats 400000 in
-- Elaborating the nested conditional-PMF kernel contract is intensive.
/-- A valid explicit-modulus cell bounds the full joint high-activity event at
an arbitrary row count and squared-norm floor. -/
theorem dominantThresholdHighActivity_le_thresholdCell_at
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (rows squaredNormFloor : ℕ) (cell : ThresholdDominantCellRowBoundsAt rows)
    (hq : Odd q) (hi : w i ≠ 0)
    (hvalid : ThresholdDominantCellRowBoundsAt.Valid cell)
    (hu_actual : 0 < dominantResidualRatio w i)
    (hlower_u : (cell.lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (cell.upper : ℝ))
    (hr : dominantThresholdRatio w i inputThreshold ≤
      (cell.thresholdUpper : ℝ))
    (hmodulus : (cell.modulusLower : ℝ) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    (eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
      thresholdDominantCellMajorantAt rows squaredNormFloor cell := by
  have hlowerReal : 0 ≤ (cell.lower : ℝ) := by
    exact_mod_cast hvalid.1
  have hmodulusLowerReal : 1 < (cell.modulusLower : ℝ) := by
    exact_mod_cast hvalid.2.2.2.1
  apply dominantThresholdHighActivity_le_cellMajorant_of_conditional_at
  intro activity
  apply
    dominantConditional_thresholdHighActivity_le_cellMajorant_of_rowKernels_at
      w i hi rows squaredNormFloor inputThreshold activity cell hvalid hr
  intro row
  exact dominantRowKernel_le_thresholdCell
    w i q cell.lower cell.upper cell.modulusLower
      (cell.z (dominantActivityCount activity)) (activity row)
      hq hi hlowerReal hu_actual hlower_u hu_upper
      (by exact_mod_cast
        hvalid.2.2.2.2 (dominantActivityCount activity))
      hmodulusLowerReal hmodulus

set_option maxHeartbeats 400000 in
-- Elaborating the nested conditional-PMF kernel contract is intensive.
/-- Compatibility specialization of explicit-modulus cell soundness at 256
rows and squared-norm floor 29. -/
theorem dominantThresholdHighActivity_le_thresholdCell
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (cell : ThresholdDominantCellRowBounds)
    (hq : Odd q) (hi : w i ≠ 0)
    (hvalid : cell.Valid)
    (hu_actual : 0 < dominantResidualRatio w i)
    (hlower_u : (cell.lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (cell.upper : ℝ))
    (hr : dominantThresholdRatio w i inputThreshold ≤
      (cell.thresholdUpper : ℝ))
    (hmodulus : (cell.modulusLower : ℝ) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    (eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal ≤
      thresholdDominantCellMajorant cell := by
  rw [thresholdDominantCellMajorant_eq_at]
  exact dominantThresholdHighActivity_le_thresholdCell_at
    w i inputThreshold 256 29 cell hq hi hvalid hu_actual hlower_u
      hu_upper hr hmodulus

end CertifiedJL
