/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedSupport
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.FourierQuantitative

/-!
# Two-mode retained Fourier bounds for the 128-bit dominant branch

This file keeps the dominant coordinate inside the unconditioned balanced-
ternary row.  Its first Fourier mode therefore sees the full retained mass,
while the second mode carries the dominant cosine factor explicitly.
-/

open scoped BigOperators

namespace CertifiedJL

/-- Isolate a unit dominant coordinate and apply the compact second-mode
envelope only to the residual coordinates. -/
theorem dominantCapped_secondModeProduct_le
    {d : ℕ} (v : Fin d → ℝ) (i : Fin d) {B u₀ : ℝ}
    (hB : 2 ≤ B) (hi : |v i| = 1)
    (hcoord : ∀ j, j ≠ i → |v j| ≤ 13 / 16)
    (hmass : u₀ ≤ ∑ j ∈ Finset.univ.erase i, (v j) ^ 2) :
    (∏ j, Real.cos (2 * Real.pi * v j / B) ^ 2) ≤
      Real.cos (2 * Real.pi / B) ^ 2 *
        Real.exp (-(7 / 200 : ℝ) * (2 * Real.pi / B) ^ 2 * u₀) := by
  let residual : Fin d → ℝ := fun j => if j = i then 0 else v j
  have hresCoord : ∀ j, |residual j| ≤ 13 / 16 := by
    intro j
    by_cases hji : j = i
    · simp [residual, hji]
      norm_num
    · simpa [residual, hji] using hcoord j hji
  have hresMass : u₀ ≤ ∑ j, (residual j) ^ 2 := by
    rw [show (∑ j, (residual j) ^ 2) =
        ∑ j ∈ Finset.univ.erase i, (v j) ^ 2 by
      calc
        (∑ j, (residual j) ^ 2) =
            (∑ j ∈ Finset.univ.erase i, (residual j) ^ 2) +
              (residual i) ^ 2 :=
          (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
        _ = ∑ j ∈ Finset.univ.erase i, (v j) ^ 2 := by
          rw [show residual i ^ 2 = 0 by simp [residual]]
          simp only [add_zero]
          apply Finset.sum_congr rfl
          intro j hj
          simp [residual, (Finset.mem_erase.1 hj).1]]
    exact hmass
  have hres := compact_secondModeProduct_le residual hB hresCoord hresMass
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hiCos :
      Real.cos (2 * Real.pi * v i / B) ^ 2 =
        Real.cos (2 * Real.pi / B) ^ 2 := by
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hi
    rcases hi with hvi | hvi
    · rw [hvi]
      congr 2
      ring
    · rw [hvi]
      ring_nf
      rw [Real.cos_neg]
  rw [hiCos]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    (∏ j ∈ Finset.univ.erase i,
        Real.cos (2 * Real.pi * v j / B) ^ 2) =
        ∏ j, Real.cos (2 * Real.pi * residual j / B) ^ 2 := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [residual, if_pos, mul_zero, zero_div, Real.cos_zero, one_pow,
        one_mul]
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (Finset.mem_erase.1 hj).1]
    _ ≤ Real.exp (-(7 / 200 : ℝ) * (2 * Real.pi / B) ^ 2 * u₀) := hres

/-- Integer-frequency form of `dominantCapped_secondModeProduct_le`. -/
theorem sparseCyclicCosineModeInt_two_le_dominantCapped
    {d : ℕ} (q A : ℕ) (w : Fin d → ℤ) (i : Fin d) (u₀ : ℝ)
    (hq : 0 < q) (hA : 0 < A)
    (hB : 2 ≤ (q : ℝ) / (A : ℝ))
    (hi : |(w i : ℝ) / (A : ℝ)| = 1)
    (hcoord : ∀ j, j ≠ i → |(w j : ℝ) / (A : ℝ)| ≤ 13 / 16)
    (hmass : u₀ ≤ ∑ j ∈ Finset.univ.erase i,
      ((w j : ℝ) / (A : ℝ)) ^ 2) :
    sparseCyclicCosineModeInt q w 2 ≤
      Real.cos (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 *
        Real.exp (-(7 / 200 : ℝ) *
          (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * u₀) := by
  rw [sparseCyclicCosineModeInt_eq_normalizedCosProduct q A w 2 hq hA]
  norm_num only [Int.cast_ofNat]
  calc
    (∏ j, Real.cos
        (Real.pi * 2 * ((w j : ℝ) / (A : ℝ)) /
          ((q : ℝ) / (A : ℝ))) ^ 2) =
        ∏ j, Real.cos
          (2 * Real.pi * ((w j : ℝ) / (A : ℝ)) /
            ((q : ℝ) / (A : ℝ))) ^ 2 := by
      apply Finset.prod_congr rfl
      intro j hj
      congr 2
      ring
    _ ≤ _ := dominantCapped_secondModeProduct_le
      (fun j => (w j : ℝ) / (A : ℝ)) i hB hi hcoord hmass

/-- Normalized two-mode row envelope for the capped retained branch. -/
noncomputable def thresholdDominantCappedFourierRow (B z : ℝ) : ℝ :=
  let c := Real.pi ^ 2 / (z * B ^ 2)
  let L₁ := Real.exp (-(Real.pi / B) ^ 2 * (3 / 2))
  let L₂ := Real.cos (2 * Real.pi / B) ^ 2 *
    Real.exp (-(7 / 200) * (2 * Real.pi / B) ^ 2 * (1 / 2))
  1 / Real.sqrt (z * B ^ 2 / Real.pi) *
    (1 + 2 * (Real.exp (-c) * L₁ + Real.exp (-4 * c) * L₂) +
      2 * (Real.exp (-9 * c) / (1 - Real.exp (-7 * c))))

/-- Conservative endpoint-separated envelope for a short modulus cell. -/
noncomputable def thresholdDominantCappedFourierCellRow
    (L U z : ℝ) : ℝ :=
  let cU := Real.pi ^ 2 / (z * U ^ 2)
  let L₁U := Real.exp (-(Real.pi / U) ^ 2 * (3 / 2))
  let L₂LU := Real.cos (2 * Real.pi / L) ^ 2 *
    Real.exp (-(7 / 200) * (2 * Real.pi / U) ^ 2 * (1 / 2))
  1 / Real.sqrt (z * L ^ 2 / Real.pi) *
    (1 + 2 * (Real.exp (-cU) * L₁U +
      Real.exp (-4 * cU) * L₂LU) +
      2 * (Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU))))

/-- On `2 ≤ L ≤ B ≤ 3`, the squared dominant second-mode phase is
largest at the lower modulus endpoint. -/
theorem dominant_secondModePhase_sq_le_lowerEndpoint
    {L B : ℝ} (hL : 2 ≤ L) (hLB : L ≤ B) (hB : B ≤ 3) :
    Real.cos (2 * Real.pi / B) ^ 2 ≤
      Real.cos (2 * Real.pi / L) ^ 2 := by
  have hLpos : 0 < L := by linarith
  have hBpos : 0 < B := hLpos.trans_le hLB
  have hxOrder : 2 * Real.pi / B ≤ 2 * Real.pi / L := by
    exact div_le_div_of_nonneg_left (by positivity) hLpos hLB
  have hxBLower : Real.pi / 2 ≤ 2 * Real.pi / B := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hBpos]
    nlinarith [Real.pi_pos]
  have hxLUpper : 2 * Real.pi / L ≤ Real.pi := by
    rw [div_le_iff₀ hLpos]
    nlinarith [Real.pi_pos]
  have hxBNonneg : 0 ≤ 2 * Real.pi / B := by positivity
  have hxLNonneg : 0 ≤ 2 * Real.pi / L := by positivity
  have hcosOrder : Real.cos (2 * Real.pi / L) ≤
      Real.cos (2 * Real.pi / B) :=
    Real.antitoneOn_cos ⟨hxBNonneg, hxOrder.trans hxLUpper⟩
      ⟨hxLNonneg, hxLUpper⟩ hxOrder
  have hcosBNonpos : Real.cos (2 * Real.pi / B) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hxBLower
      (by linarith [hxOrder, hxLUpper, Real.pi_pos])
  nlinarith [sq_nonneg
    (Real.cos (2 * Real.pi / B) - Real.cos (2 * Real.pi / L))]

private theorem fourierRate_anti
    {B U z : ℝ} (hB : 0 < B) (hBU : B ≤ U) (hz : 0 < z) :
    Real.pi ^ 2 / (z * U ^ 2) ≤ Real.pi ^ 2 / (z * B ^ 2) := by
  have hU : 0 < U := hB.trans_le hBU
  apply div_le_div_of_nonneg_left (sq_nonneg Real.pi)
  · positivity
  · exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hB.le hU.le).2 hBU) hz.le

/-- The endpoint-separated cell expression soundly dominates every modulus
inside the cell. -/
theorem thresholdDominantCappedFourierRow_le_cell
    {L B U z : ℝ} (hL : 2 ≤ L) (hLB : L ≤ B) (hBU : B ≤ U)
    (hU : U ≤ 3) (hz : 0 < z) :
    thresholdDominantCappedFourierRow B z ≤
      thresholdDominantCappedFourierCellRow L U z := by
  have hLpos : 0 < L := by linarith
  have hBpos : 0 < B := hLpos.trans_le hLB
  have hUpos : 0 < U := hBpos.trans_le hBU
  let cB : ℝ := Real.pi ^ 2 / (z * B ^ 2)
  let cU : ℝ := Real.pi ^ 2 / (z * U ^ 2)
  have hcB : 0 < cB := by dsimp [cB]; positivity
  have hcU : 0 < cU := by dsimp [cU]; positivity
  have hc : cU ≤ cB := fourierRate_anti hBpos hBU hz
  have hprefactor :
      1 / Real.sqrt (z * B ^ 2 / Real.pi) ≤
        1 / Real.sqrt (z * L ^ 2 / Real.pi) := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hLpos.le hBpos.le).2 hLB) hz.le
    · exact Real.pi_pos.le
  have hexpC : Real.exp (-cB) ≤ Real.exp (-cU) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hexpFourC : Real.exp (-4 * cB) ≤ Real.exp (-4 * cU) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hpiDiv : (Real.pi / U) ^ 2 ≤ (Real.pi / B) ^ 2 := by
    have hdiv : Real.pi / U ≤ Real.pi / B :=
      div_le_div_of_nonneg_left Real.pi_pos.le hBpos hBU
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hdiv
  have htwoPiDiv : (2 * Real.pi / U) ^ 2 ≤
      (2 * Real.pi / B) ^ 2 := by
    have hdiv : 2 * Real.pi / U ≤ 2 * Real.pi / B :=
      div_le_div_of_nonneg_left (by positivity) hBpos hBU
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hdiv
  have hmodeOne :
      Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) ≤
        Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hphase := dominant_secondModePhase_sq_le_lowerEndpoint
    hL hLB (hBU.trans hU)
  have hresidual :
      Real.exp (-(7 / 200) * (2 * Real.pi / B) ^ 2 * (1 / 2)) ≤
        Real.exp (-(7 / 200) * (2 * Real.pi / U) ^ 2 * (1 / 2)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hfirstTerm :
      Real.exp (-cB) * Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) ≤
        Real.exp (-cU) * Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) :=
    mul_le_mul hexpC hmodeOne (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hsecondMode :
      Real.cos (2 * Real.pi / B) ^ 2 *
          Real.exp (-(7 / 200) * (2 * Real.pi / B) ^ 2 * (1 / 2)) ≤
        Real.cos (2 * Real.pi / L) ^ 2 *
          Real.exp (-(7 / 200) * (2 * Real.pi / U) ^ 2 * (1 / 2)) :=
    mul_le_mul hphase hresidual (Real.exp_nonneg _) (sq_nonneg _)
  have hsecondTerm :
      Real.exp (-4 * cB) *
          (Real.cos (2 * Real.pi / B) ^ 2 *
            Real.exp (-(7 / 200) * (2 * Real.pi / B) ^ 2 * (1 / 2))) ≤
        Real.exp (-4 * cU) *
          (Real.cos (2 * Real.pi / L) ^ 2 *
            Real.exp (-(7 / 200) * (2 * Real.pi / U) ^ 2 * (1 / 2))) :=
    mul_le_mul hexpFourC hsecondMode
      (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hnum : Real.exp (-9 * cB) ≤ Real.exp (-9 * cU) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hdenOrder : 1 - Real.exp (-7 * cU) ≤
      1 - Real.exp (-7 * cB) := by
    have : Real.exp (-7 * cB) ≤ Real.exp (-7 * cU) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hdenU : 0 < 1 - Real.exp (-7 * cU) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have htail : Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB)) ≤
      Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU)) := by
    exact div_le_div₀ (Real.exp_nonneg _) hnum hdenU hdenOrder
  have hinside :
      1 + 2 *
          (Real.exp (-cB) * Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) +
            Real.exp (-4 * cB) *
              (Real.cos (2 * Real.pi / B) ^ 2 *
                Real.exp (-(7 / 200) * (2 * Real.pi / B) ^ 2 * (1 / 2)))) +
          2 * (Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB))) ≤
        1 + 2 *
          (Real.exp (-cU) * Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) +
            Real.exp (-4 * cU) *
              (Real.cos (2 * Real.pi / L) ^ 2 *
                Real.exp (-(7 / 200) * (2 * Real.pi / U) ^ 2 * (1 / 2)))) +
          2 * (Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU))) := by
    gcongr
  have hinsideNonneg : 0 ≤
      1 + 2 *
          (Real.exp (-cB) * Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) +
            Real.exp (-4 * cB) *
              (Real.cos (2 * Real.pi / B) ^ 2 *
                Real.exp (-(7 / 200) * (2 * Real.pi / B) ^ 2 * (1 / 2)))) +
          2 * (Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB))) := by
    have hdenB : 0 < 1 - Real.exp (-7 * cB) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    positivity
  unfold thresholdDominantCappedFourierRow
    thresholdDominantCappedFourierCellRow
  dsimp only
  change 1 / Real.sqrt (z * B ^ 2 / Real.pi) * _ ≤
    1 / Real.sqrt (z * L ^ 2 / Real.pi) * _
  exact mul_le_mul hprefactor hinside hinsideNonneg (by positivity)

/-- Wrapped expectation of a retained profile with a unit dominant coordinate
and capped residual mass at least one half. -/
theorem sparseRow_wrappedGaussianKernel_le_dominantCappedTwoMode
    {q d : ℕ} (A : ℕ) (w : Fin d → ℤ) (i : Fin d) {z : ℝ}
    (hq : 0 < q) (hA : 0 < A) (hz : 0 < z)
    (hB : 2 < (q : ℝ) / (A : ℝ))
    (hi : |(w i : ℝ) / (A : ℝ)| = 1)
    (hcoordOne : ∀ j, |(w j : ℝ) / (A : ℝ)| ≤ 1)
    (hcoordCap : ∀ j, j ≠ i → |(w j : ℝ) / (A : ℝ)| ≤ 13 / 16)
    (hmassFull : (3 / 2 : ℝ) ≤ ∑ j, ((w j : ℝ) / (A : ℝ)) ^ 2)
    (hmassResidual : (1 / 2 : ℝ) ≤ ∑ j ∈ Finset.univ.erase i,
      ((w j : ℝ) / (A : ℝ)) ^ 2) :
    (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
        (∑ j, row j * w j) ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantCappedFourierRow ((q : ℝ) / (A : ℝ)) z := by
  have hs : 0 < z / (A : ℝ) ^ 2 := by positivity
  have hmode₁ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 1 ≤
        Real.exp (-((Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2) * (3 / 2)) := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_one_le_compactMass q A w (3 / 2)
        hq hA hB hcoordOne hmassFull
  have hmode₂ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 2 ≤
        Real.cos (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 *
          Real.exp (-(7 / 200 : ℝ) *
            (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * (1 / 2)) := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_two_le_dominantCapped
        q A w i (1 / 2) hq hA hB.le hi hcoordCap hmassResidual
  have htwo := sparseRow_shiftedWrappedGaussianKernel_le_twoMode
    (q := q) 0 w hq hs hmode₁ hmode₂
  have hAreal : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hscale :
      (z / (A : ℝ) ^ 2) * (q : ℝ) ^ 2 / Real.pi =
        z * ((q : ℝ) / (A : ℝ)) ^ 2 / Real.pi := by
    field_simp [hAreal, hqreal]
  have hc :
      Real.pi ^ 2 / ((z / (A : ℝ) ^ 2) * (q : ℝ) ^ 2) =
        Real.pi ^ 2 / (z * ((q : ℝ) / (A : ℝ)) ^ 2) := by
    field_simp [hAreal, hqreal, hz.ne']
  simp only [zero_add] at htwo
  rw [hscale, hc] at htwo
  simpa [thresholdDominantCappedFourierRow] using htwo

/-- Selective-Fourier transport for the capped half-mass branch. -/
theorem sparseRow_centeredGaussian_le_dominantCappedFourierRow
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (support : Finset
      (Fin (Fintype.card (DominantRemainderIndex i)))) {z : ℝ}
    (hq : Odd q) (hi : w i ≠ 0) (hz : 0 < z)
    (hB : 2 < (q : ℝ) / (dominantAmplitude w i : ℝ))
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hlower : dominantAmplitude w i ^ 2 ≤
      2 * sqNorm (fun j => if j ∈ support then
        dominantRemainderFinWeights w i j else 0))
    (hcap : ∀ j, 16 * (dominantRemainderFinWeights w i j).natAbs ≤
      13 * dominantAmplitude w i) :
    (∫ row, Real.exp (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
        sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantCappedFourierRow
        ((q : ℝ) / (dominantAmplitude w i : ℝ)) z := by
  let A := dominantAmplitude w i
  let V := sqNorm (fun j => if j ∈ support then
    dominantRemainderFinWeights w i j else 0)
  let compact : Fin d → ℤ := fun j =>
    if j ∈ dominantLiftSupport i support then w j else 0
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hcompactI : compact i = w i := by simp [compact]
  have hiSq : (compact i : ℝ) ^ 2 = (A : ℝ) ^ 2 := by
    rw [hcompactI]
    dsimp [A, dominantAmplitude]
    have habs : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs, sq_abs]
  have hcompactResidual : dominantRemainderFinWeights compact i =
      fun j => if j ∈ support then dominantRemainderFinWeights w i j else 0 :=
    dominantRemainderFinWeights_restrict_liftSupport w i support
  have hcompactSq : ∑ j, (compact j : ℝ) ^ 2 = (A : ℝ) ^ 2 + V := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
    have hreindex :
        (∑ j : DominantRemainderIndex i, (compact j.1 : ℝ) ^ 2) =
          ∑ k, (dominantRemainderFinWeights compact i k : ℝ) ^ 2 := by
      exact ((dominantRemainderEquivFin i).symm.sum_comp
        (fun j : DominantRemainderIndex i => (compact j.1 : ℝ) ^ 2)).symm
    rw [hreindex, hcompactResidual]
    have hres :
        (∑ k, ((fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) k : ℝ) ^ 2) =
            (V : ℝ) := by
      simpa only [V] using (realCast_sqNorm
        (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0)).symm
    rw [hres, hiSq]
  have hcompactEraseSq :
      ∑ j ∈ Finset.univ.erase i, (compact j : ℝ) ^ 2 = (V : ℝ) := by
    have hsum := hcompactSq
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    rw [hiSq] at hsum
    linarith
  have hunit : |(compact i : ℝ) / (A : ℝ)| = 1 := by
    rw [abs_div, abs_of_pos hAreal]
    have habs : |(compact i : ℝ)| = (A : ℝ) := by
      rw [hcompactI]
      dsimp [A, dominantAmplitude]
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs, div_self hAreal.ne']
  have hcoordOne : ∀ j, |(compact j : ℝ) / (A : ℝ)| ≤ 1 := by
    intro j
    rw [abs_div, abs_of_pos hAreal, div_le_one hAreal]
    by_cases hj : j ∈ dominantLiftSupport i support
    · rw [show compact j = w j by simp [compact, hj]]
      have hnatReal : ((w j).natAbs : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 := by
        exact_mod_cast hmax j
      have habs : ((w j).natAbs : ℝ) = |(w j : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [habs] at hnatReal
      nlinarith [abs_nonneg (w j : ℝ)]
    · simp [compact, hj, hAreal.le]
  have hcoordCap : ∀ j, j ≠ i →
      |(compact j : ℝ) / (A : ℝ)| ≤ 13 / 16 := by
    intro j hji
    rw [abs_div, abs_of_pos hAreal]
    by_cases hj : j ∈ dominantLiftSupport i support
    · rw [show compact j = w j by simp [compact, hj]]
      have hnat := dominantRemainder_coordinate_cap_of_fin_cap
        w i j hji hcap
      have hnatReal : (16 : ℝ) * ((w j).natAbs : ℝ) ≤ 13 * A := by
        exact_mod_cast hnat
      have habs : ((w j).natAbs : ℝ) = |(w j : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [habs] at hnatReal
      apply (div_le_iff₀ hAreal).2
      nlinarith
    · simp [compact, hj]
      norm_num
  have hmassFull : (3 / 2 : ℝ) ≤
      ∑ j, ((compact j : ℝ) / (A : ℝ)) ^ 2 := by
    have hlowerReal : (A : ℝ) ^ 2 ≤ 2 * (V : ℝ) := by
      exact_mod_cast hlower
    rw [show (∑ j, ((compact j : ℝ) / (A : ℝ)) ^ 2) =
        ((A : ℝ) ^ 2 + V) / (A : ℝ) ^ 2 by
      rw [← hcompactSq, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_pow]]
    apply (le_div_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  have hmassResidual : (1 / 2 : ℝ) ≤
      ∑ j ∈ Finset.univ.erase i,
        ((compact j : ℝ) / (A : ℝ)) ^ 2 := by
    have hlowerReal : (A : ℝ) ^ 2 ≤ 2 * (V : ℝ) := by
      exact_mod_cast hlower
    rw [show (∑ j ∈ Finset.univ.erase i,
        ((compact j : ℝ) / (A : ℝ)) ^ 2) =
          (V : ℝ) / (A : ℝ) ^ 2 by
      rw [← hcompactEraseSq, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_pow]]
    apply (le_div_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  have htransport := sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict
    w (dominantLiftSupport i support) hq
      (by positivity : 0 < z / (A : ℝ) ^ 2)
  have hwrapped := sparseRow_wrappedGaussianKernel_le_dominantCappedTwoMode
    A compact i hq.pos hA hz hB hunit hcoordOne hcoordCap
      hmassFull hmassResidual
  exact htransport.trans (by simpa only [compact, A] using hwrapped)

end CertifiedJL
