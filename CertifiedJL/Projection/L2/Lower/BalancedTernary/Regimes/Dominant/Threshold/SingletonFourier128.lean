/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedFourier128

/-! # Two-mode bounds for the large retained singleton branch -/

open scoped BigOperators

namespace CertifiedJL

/-- A deliberately coarse two-mode row envelope for the resonant half of the
large-singleton branch.  The first mode retains the total mass lower bound;
the second mode is bounded only by one. -/
noncomputable def thresholdDominantSingletonLowFourierRow (B z : ℝ) : ℝ :=
  let c := Real.pi ^ 2 / (z * B ^ 2)
  let L₁ := Real.exp (-(Real.pi / B) ^ 2 * (3 / 2))
  1 / Real.sqrt (z * B ^ 2 / Real.pi) *
    (1 + 2 * (Real.exp (-c) * L₁ + Real.exp (-4 * c)) +
      2 * (Real.exp (-9 * c) / (1 - Real.exp (-7 * c))))

/-- Endpoint-separated envelope on a short modulus cell. -/
noncomputable def thresholdDominantSingletonLowFourierCellRow
    (L U z : ℝ) : ℝ :=
  let cU := Real.pi ^ 2 / (z * U ^ 2)
  let L₁U := Real.exp (-(Real.pi / U) ^ 2 * (3 / 2))
  1 / Real.sqrt (z * L ^ 2 / Real.pi) *
    (1 + 2 * (Real.exp (-cU) * L₁U + Real.exp (-4 * cU)) +
      2 * (Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU))))

private theorem singleton_fourierRate_anti
    {B U z : ℝ} (hB : 0 < B) (hBU : B ≤ U) (hz : 0 < z) :
    Real.pi ^ 2 / (z * U ^ 2) ≤ Real.pi ^ 2 / (z * B ^ 2) := by
  have hU : 0 < U := hB.trans_le hBU
  apply div_le_div_of_nonneg_left (sq_nonneg Real.pi)
  · positivity
  · exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hB.le hU.le).2 hBU) hz.le

/-- The endpoint-separated low-singleton cell dominates every row inside it. -/
theorem thresholdDominantSingletonLowFourierRow_le_cell
    {L B U z : ℝ} (hL : 0 < L) (hLB : L ≤ B) (hBU : B ≤ U)
    (hz : 0 < z) :
    thresholdDominantSingletonLowFourierRow B z ≤
      thresholdDominantSingletonLowFourierCellRow L U z := by
  have hB : 0 < B := hL.trans_le hLB
  have hU : 0 < U := hB.trans_le hBU
  let cB : ℝ := Real.pi ^ 2 / (z * B ^ 2)
  let cU : ℝ := Real.pi ^ 2 / (z * U ^ 2)
  have hcB : 0 < cB := by dsimp [cB]; positivity
  have hcU : 0 < cU := by dsimp [cU]; positivity
  have hc : cU ≤ cB := singleton_fourierRate_anti hB hBU hz
  have hprefactor :
      1 / Real.sqrt (z * B ^ 2 / Real.pi) ≤
        1 / Real.sqrt (z * L ^ 2 / Real.pi) := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hL.le hB.le).2 hLB) hz.le
    · exact Real.pi_pos.le
  have hexpC : Real.exp (-cB) ≤ Real.exp (-cU) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexpFour : Real.exp (-4 * cB) ≤ Real.exp (-4 * cU) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpiDiv : (Real.pi / U) ^ 2 ≤ (Real.pi / B) ^ 2 := by
    have hdiv : Real.pi / U ≤ Real.pi / B :=
      div_le_div_of_nonneg_left Real.pi_pos.le hB hBU
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hdiv
  have hmodeOne :
      Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) ≤
        Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hfirst :
      Real.exp (-cB) * Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) ≤
        Real.exp (-cU) * Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) :=
    mul_le_mul hexpC hmodeOne (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hnum : Real.exp (-9 * cB) ≤ Real.exp (-9 * cU) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hdenOrder : 1 - Real.exp (-7 * cU) ≤
      1 - Real.exp (-7 * cB) := by
    have : Real.exp (-7 * cB) ≤ Real.exp (-7 * cU) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hdenU : 0 < 1 - Real.exp (-7 * cU) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have htail : Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB)) ≤
      Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU)) :=
    div_le_div₀ (Real.exp_nonneg _) hnum hdenU hdenOrder
  have hinside :
      1 + 2 * (Real.exp (-cB) *
          Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) + Real.exp (-4 * cB)) +
          2 * (Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB))) ≤
        1 + 2 * (Real.exp (-cU) *
          Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) + Real.exp (-4 * cU)) +
          2 * (Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU))) := by
    gcongr
  have hinsideNonneg : 0 ≤
      1 + 2 * (Real.exp (-cB) *
          Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) + Real.exp (-4 * cB)) +
          2 * (Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB))) := by
    have hdenB : 0 < 1 - Real.exp (-7 * cB) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    positivity
  unfold thresholdDominantSingletonLowFourierRow
    thresholdDominantSingletonLowFourierCellRow
  dsimp only
  exact mul_le_mul hprefactor hinside hinsideNonneg (by positivity)

/-- A sharper low-singleton envelope which retains the squared second-mode
phase contributed by the unit dominant coordinate. -/
noncomputable def thresholdDominantSingletonPhaseFourierRow (B z : ℝ) : ℝ :=
  let c := Real.pi ^ 2 / (z * B ^ 2)
  let L₁ := Real.exp (-(Real.pi / B) ^ 2 * (3 / 2))
  let L₂ := Real.cos (2 * Real.pi / B) ^ 2
  1 / Real.sqrt (z * B ^ 2 / Real.pi) *
    (1 + 2 * (Real.exp (-c) * L₁ + Real.exp (-4 * c) * L₂) +
      2 * (Real.exp (-9 * c) / (1 - Real.exp (-7 * c))))

/-- Endpoint-separated cell envelope for the phase-retaining singleton row. -/
noncomputable def thresholdDominantSingletonPhaseFourierCellRow
    (L U z : ℝ) : ℝ :=
  let cU := Real.pi ^ 2 / (z * U ^ 2)
  let L₁U := Real.exp (-(Real.pi / U) ^ 2 * (3 / 2))
  let L₂L := Real.cos (2 * Real.pi / L) ^ 2
  1 / Real.sqrt (z * L ^ 2 / Real.pi) *
    (1 + 2 * (Real.exp (-cU) * L₁U + Real.exp (-4 * cU) * L₂L) +
      2 * (Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU))))

/-- The phase-retaining cell dominates every row in a cell contained in
`[2,3]`. -/
theorem thresholdDominantSingletonPhaseFourierRow_le_cell
    {L B U z : ℝ} (hL : 2 ≤ L) (hLB : L ≤ B) (hBU : B ≤ U)
    (hU : U ≤ 3) (hz : 0 < z) :
    thresholdDominantSingletonPhaseFourierRow B z ≤
      thresholdDominantSingletonPhaseFourierCellRow L U z := by
  have hLpos : 0 < L := by linarith
  have hBpos : 0 < B := hLpos.trans_le hLB
  have hUpos : 0 < U := hBpos.trans_le hBU
  let cB : ℝ := Real.pi ^ 2 / (z * B ^ 2)
  let cU : ℝ := Real.pi ^ 2 / (z * U ^ 2)
  have hcB : 0 < cB := by dsimp [cB]; positivity
  have hcU : 0 < cU := by dsimp [cU]; positivity
  have hc : cU ≤ cB := singleton_fourierRate_anti hBpos hBU hz
  have hprefactor :
      1 / Real.sqrt (z * B ^ 2 / Real.pi) ≤
        1 / Real.sqrt (z * L ^ 2 / Real.pi) := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hLpos.le hBpos.le).2 hLB) hz.le
    · exact Real.pi_pos.le
  have hexpC : Real.exp (-cB) ≤ Real.exp (-cU) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexpFour : Real.exp (-4 * cB) ≤ Real.exp (-4 * cU) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpiDiv : (Real.pi / U) ^ 2 ≤ (Real.pi / B) ^ 2 := by
    have hdiv : Real.pi / U ≤ Real.pi / B :=
      div_le_div_of_nonneg_left Real.pi_pos.le hBpos hBU
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hdiv
  have hmodeOne :
      Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) ≤
        Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hphase := dominant_secondModePhase_sq_le_lowerEndpoint
    hL hLB (hBU.trans hU)
  have hfirst :
      Real.exp (-cB) * Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) ≤
        Real.exp (-cU) * Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) :=
    mul_le_mul hexpC hmodeOne (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hsecond :
      Real.exp (-4 * cB) * Real.cos (2 * Real.pi / B) ^ 2 ≤
        Real.exp (-4 * cU) * Real.cos (2 * Real.pi / L) ^ 2 :=
    mul_le_mul hexpFour hphase (sq_nonneg _) (Real.exp_nonneg _)
  have hnum : Real.exp (-9 * cB) ≤ Real.exp (-9 * cU) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hdenOrder : 1 - Real.exp (-7 * cU) ≤
      1 - Real.exp (-7 * cB) := by
    have : Real.exp (-7 * cB) ≤ Real.exp (-7 * cU) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hdenU : 0 < 1 - Real.exp (-7 * cU) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have htail : Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB)) ≤
      Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU)) :=
    div_le_div₀ (Real.exp_nonneg _) hnum hdenU hdenOrder
  have hinside :
      1 + 2 * (Real.exp (-cB) *
          Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) +
            Real.exp (-4 * cB) * Real.cos (2 * Real.pi / B) ^ 2) +
          2 * (Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB))) ≤
        1 + 2 * (Real.exp (-cU) *
          Real.exp (-(Real.pi / U) ^ 2 * (3 / 2)) +
            Real.exp (-4 * cU) * Real.cos (2 * Real.pi / L) ^ 2) +
          2 * (Real.exp (-9 * cU) / (1 - Real.exp (-7 * cU))) := by
    gcongr
  have hinsideNonneg : 0 ≤
      1 + 2 * (Real.exp (-cB) *
          Real.exp (-(Real.pi / B) ^ 2 * (3 / 2)) +
            Real.exp (-4 * cB) * Real.cos (2 * Real.pi / B) ^ 2) +
          2 * (Real.exp (-9 * cB) / (1 - Real.exp (-7 * cB))) := by
    have hdenB : 0 < 1 - Real.exp (-7 * cB) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    positivity
  unfold thresholdDominantSingletonPhaseFourierRow
    thresholdDominantSingletonPhaseFourierCellRow
  dsimp only
  exact mul_le_mul hprefactor hinside hinsideNonneg (by positivity)

/-- A cosine-square product is at most the factor contributed by any
coordinate. -/
private theorem dominantCoordinate_cosineProduct_le
    {d : ℕ} (v : Fin d → ℝ) (i : Fin d) (x : ℝ) :
    (∏ j, Real.cos (x * v j) ^ 2) ≤ Real.cos (x * v i) ^ 2 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hprod : (∏ j ∈ Finset.univ.erase i,
      Real.cos (x * v j) ^ 2) ≤ 1 := by
    apply Finset.prod_le_one
    · intro j _
      exact sq_nonneg _
    · intro j _
      nlinarith [Real.neg_one_le_cos (x * v j), Real.cos_le_one (x * v j)]
  calc
    Real.cos (x * v i) ^ 2 *
        (∏ j ∈ Finset.univ.erase i, Real.cos (x * v j) ^ 2) ≤
      Real.cos (x * v i) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = Real.cos (x * v i) ^ 2 := mul_one _

/-- Integer-frequency second-mode bound retaining the unit dominant phase. -/
theorem sparseCyclicCosineModeInt_two_le_dominantPhase
    {d : ℕ} (q A : ℕ) (w : Fin d → ℤ) (i : Fin d)
    (hq : 0 < q) (hA : 0 < A)
    (hi : |(w i : ℝ) / (A : ℝ)| = 1) :
    sparseCyclicCosineModeInt q w 2 ≤
      Real.cos (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 := by
  rw [sparseCyclicCosineModeInt_eq_normalizedCosProduct q A w 2 hq hA]
  norm_num only [Int.cast_ofNat]
  calc
    (∏ j, Real.cos
        (Real.pi * 2 * ((w j : ℝ) / (A : ℝ)) /
          ((q : ℝ) / (A : ℝ))) ^ 2) =
        ∏ j, Real.cos
          ((2 * Real.pi / ((q : ℝ) / (A : ℝ))) *
            ((w j : ℝ) / (A : ℝ))) ^ 2 := by
      apply Finset.prod_congr rfl
      intro j hj
      congr 2
      ring
    _ ≤ Real.cos
        ((2 * Real.pi / ((q : ℝ) / (A : ℝ))) *
          ((w i : ℝ) / (A : ℝ))) ^ 2 :=
      dominantCoordinate_cosineProduct_le _ i _
    _ = Real.cos (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 := by
      rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hi
      rcases hi with hi | hi
      · rw [hi]
        ring_nf
      · rw [hi]
        ring_nf
        rw [Real.cos_neg]

/-- A wrapped row with a unit dominant coordinate and total normalized mass
at least `3/2` obeys the phase-retaining singleton envelope. -/
theorem sparseRow_wrappedGaussianKernel_le_dominantSingletonPhaseTwoMode
    {q d : ℕ} (A : ℕ) (w : Fin d → ℤ) (i : Fin d) {z : ℝ}
    (hq : 0 < q) (hA : 0 < A) (hz : 0 < z)
    (hB : 2 < (q : ℝ) / (A : ℝ))
    (hi : |(w i : ℝ) / (A : ℝ)| = 1)
    (hcoordOne : ∀ j, |(w j : ℝ) / (A : ℝ)| ≤ 1)
    (hmassFull : (3 / 2 : ℝ) ≤ ∑ j, ((w j : ℝ) / (A : ℝ)) ^ 2) :
    (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
        (∑ j, row j * w j) ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantSingletonPhaseFourierRow
        ((q : ℝ) / (A : ℝ)) z := by
  have hs : 0 < z / (A : ℝ) ^ 2 := by positivity
  have hmode₁ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 1 ≤
        Real.exp (-((Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2) * (3 / 2)) := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_one_le_compactMass q A w (3 / 2)
        hq hA hB hcoordOne hmassFull
  have hmode₂ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 2 ≤
        Real.cos (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_two_le_dominantPhase q A w i hq hA hi
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
  simpa [thresholdDominantSingletonPhaseFourierRow] using htwo

/-- A wrapped row with a unit dominant coordinate and total normalized mass
at least `3/2` obeys the coarse singleton envelope. -/
theorem sparseRow_wrappedGaussianKernel_le_dominantSingletonLowTwoMode
    {q d : ℕ} (A : ℕ) (w : Fin d → ℤ) {z : ℝ}
    (hq : 0 < q) (hA : 0 < A) (hz : 0 < z)
    (hB : 2 < (q : ℝ) / (A : ℝ))
    (hcoordOne : ∀ j, |(w j : ℝ) / (A : ℝ)| ≤ 1)
    (hmassFull : (3 / 2 : ℝ) ≤ ∑ j, ((w j : ℝ) / (A : ℝ)) ^ 2) :
    (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
        (∑ j, row j * w j) ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantSingletonLowFourierRow
        ((q : ℝ) / (A : ℝ)) z := by
  have hs : 0 < z / (A : ℝ) ^ 2 := by positivity
  have hmode₁ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 1 ≤
        Real.exp (-((Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2) * (3 / 2)) := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_one_le_compactMass q A w (3 / 2)
        hq hA hB hcoordOne hmassFull
  have hmode₂ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 2 ≤ 1 := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_le_one q w 2
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
  simpa [thresholdDominantSingletonLowFourierRow] using htwo

/-- Isolate a unit dominant coordinate and use the full-coordinate second-mode
rate on a residual profile once the normalized modulus is at least `5/2`. -/
theorem dominantFullResidual_secondModeProduct_le
    {d : ℕ} (v : Fin d → ℝ) (i : Fin d) {B u₀ : ℝ}
    (hB : 5 / 2 ≤ B) (hi : |v i| = 1)
    (hcoord : ∀ j, j ≠ i → |v j| ≤ 1)
    (hmass : u₀ ≤ ∑ j ∈ Finset.univ.erase i, (v j) ^ 2) :
    (∏ j, Real.cos (2 * Real.pi * v j / B) ^ 2) ≤
      Real.cos (2 * Real.pi / B) ^ 2 *
        Real.exp (-(1 / 20 : ℝ) * (2 * Real.pi / B) ^ 2 * u₀) := by
  let residual : Fin d → ℝ := fun j => if j = i then 0 else v j
  have hresCoord : ∀ j, |residual j| ≤ 1 := by
    intro j
    by_cases hji : j = i
    · simp [residual, hji]
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
  have hres := full_secondModeProduct_le residual hB hresCoord hresMass
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
    _ ≤ Real.exp (-(1 / 20 : ℝ) *
        (2 * Real.pi / B) ^ 2 * u₀) := hres

/-- The large-singleton residual has enough second-mode mass to imply the
same deliberately weaker envelope used by the capped retained branch. -/
theorem dominantLargeSingleton_secondModeProduct_le_capped
    {d : ℕ} (v : Fin d → ℝ) (i : Fin d) {B : ℝ}
    (hB : 5 / 2 ≤ B) (hi : |v i| = 1)
    (hcoord : ∀ j, j ≠ i → |v j| ≤ 1)
    (hmass : (169 / 256 : ℝ) ≤
      ∑ j ∈ Finset.univ.erase i, (v j) ^ 2) :
    (∏ j, Real.cos (2 * Real.pi * v j / B) ^ 2) ≤
      Real.cos (2 * Real.pi / B) ^ 2 *
        Real.exp (-(7 / 200 : ℝ) *
          (2 * Real.pi / B) ^ 2 * (1 / 2)) := by
  have hfull := dominantFullResidual_secondModeProduct_le
    v i hB hi hcoord hmass
  apply hfull.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hsquare : 0 ≤ (2 * Real.pi / B) ^ 2 := sq_nonneg _
  nlinarith

/-- Integer-frequency form of the large-singleton second-mode estimate. -/
theorem sparseCyclicCosineModeInt_two_le_dominantLargeSingleton
    {d : ℕ} (q A : ℕ) (w : Fin d → ℤ) (i : Fin d)
    (hq : 0 < q) (hA : 0 < A)
    (hB : 5 / 2 ≤ (q : ℝ) / (A : ℝ))
    (hi : |(w i : ℝ) / (A : ℝ)| = 1)
    (hcoord : ∀ j, j ≠ i → |(w j : ℝ) / (A : ℝ)| ≤ 1)
    (hmass : (169 / 256 : ℝ) ≤ ∑ j ∈ Finset.univ.erase i,
      ((w j : ℝ) / (A : ℝ)) ^ 2) :
    sparseCyclicCosineModeInt q w 2 ≤
      Real.cos (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 *
        Real.exp (-(7 / 200 : ℝ) *
          (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * (1 / 2)) := by
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
    _ ≤ _ := dominantLargeSingleton_secondModeProduct_le_capped
      (fun j => (w j : ℝ) / (A : ℝ)) i hB hi hcoord hmass

/-- Above normalized modulus `5/2`, a large retained singleton obeys the
same row envelope as the capped retained profile. -/
theorem sparseRow_wrappedGaussianKernel_le_dominantLargeSingletonTwoMode
    {q d : ℕ} (A : ℕ) (w : Fin d → ℤ) (i : Fin d) {z : ℝ}
    (hq : 0 < q) (hA : 0 < A) (hz : 0 < z)
    (hB : 5 / 2 ≤ (q : ℝ) / (A : ℝ))
    (hi : |(w i : ℝ) / (A : ℝ)| = 1)
    (hcoordOne : ∀ j, |(w j : ℝ) / (A : ℝ)| ≤ 1)
    (hmassFull : (3 / 2 : ℝ) ≤ ∑ j, ((w j : ℝ) / (A : ℝ)) ^ 2)
    (hmassResidual : (169 / 256 : ℝ) ≤
      ∑ j ∈ Finset.univ.erase i, ((w j : ℝ) / (A : ℝ)) ^ 2) :
    (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
        (∑ j, row j * w j) ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantCappedFourierRow ((q : ℝ) / (A : ℝ)) z := by
  have hs : 0 < z / (A : ℝ) ^ 2 := by positivity
  have hmode₁ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 1 ≤
        Real.exp (-((Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2) * (3 / 2)) := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_one_le_compactMass q A w (3 / 2)
        hq hA (by linarith) hcoordOne hmassFull
  have hmode₂ :
      nonnegativeShiftedSparseCyclicCosineModeInt q 0 w 2 ≤
        Real.cos (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 *
          Real.exp (-(7 / 200 : ℝ) *
            (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * (1 / 2)) := by
    simpa [nonnegativeShiftedSparseCyclicCosineModeInt] using
      sparseCyclicCosineModeInt_two_le_dominantLargeSingleton
        q A w i hq hA hB hi (fun j _ => hcoordOne j) hmassResidual
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

/-- The retained two-coordinate profile associated to a canonical residual
witness. -/
noncomputable def dominantSingletonProfile {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (j : Fin (Fintype.card (DominantRemainderIndex i))) :
    Fin d → ℤ := fun k =>
  if k ∈ dominantLiftSupport i ({j} : Finset _) then w k else 0

@[simp] theorem dominantSingletonProfile_at_i {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (j : Fin (Fintype.card (DominantRemainderIndex i))) :
    dominantSingletonProfile w i j i = w i := by
  simp [dominantSingletonProfile]

theorem dominantSingletonProfile_remainder {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (j : Fin (Fintype.card (DominantRemainderIndex i))) :
    dominantRemainderFinWeights (dominantSingletonProfile w i j) i =
      fun k => if k = j then dominantRemainderFinWeights w i k else 0 := by
  rw [show (fun k => if k = j then dominantRemainderFinWeights w i k else 0) =
      (fun k => if k ∈ ({j} : Finset _) then
        dominantRemainderFinWeights w i k else 0) by
    funext k
    simp]
  exact dominantRemainderFinWeights_restrict_liftSupport w i {j}

/-- Exact total squared mass of the retained two-coordinate profile. -/
theorem dominantSingletonProfile_sq_sum {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (j : Fin (Fintype.card (DominantRemainderIndex i))) :
    ∑ k, (dominantSingletonProfile w i j k : ℝ) ^ 2 =
      (dominantAmplitude w i : ℝ) ^ 2 +
        ((dominantRemainderFinWeights w i j).natAbs : ℝ) ^ 2 := by
  let compact := dominantSingletonProfile w i j
  let A := dominantAmplitude w i
  have hiSq : (compact i : ℝ) ^ 2 = (A : ℝ) ^ 2 := by
    rw [show compact i = w i by simp [compact]]
    dsimp [A, dominantAmplitude]
    have habs : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs, sq_abs]
  have hres := dominantSingletonProfile_remainder w i j
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
  have hreindex :
      (∑ k : DominantRemainderIndex i, (compact k.1 : ℝ) ^ 2) =
        ∑ k, (dominantRemainderFinWeights compact i k : ℝ) ^ 2 := by
    exact ((dominantRemainderEquivFin i).symm.sum_comp
      (fun k : DominantRemainderIndex i => (compact k.1 : ℝ) ^ 2)).symm
  rw [hreindex]
  change (compact i : ℝ) ^ 2 + _ = _
  rw [hiSq]
  congr 1
  rw [hres]
  calc
    (∑ k, (((if k = j then dominantRemainderFinWeights w i k else 0) : ℤ) : ℝ) ^
        (2 : ℕ)) =
        ((dominantRemainderFinWeights w i j : ℤ) : ℝ) ^ 2 := by simp
    _ = ((dominantRemainderFinWeights w i j).natAbs : ℝ) ^ 2 := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]

/-- Exact residual squared mass after deleting the dominant coordinate. -/
theorem dominantSingletonProfile_erase_sq_sum {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (j : Fin (Fintype.card (DominantRemainderIndex i))) :
    ∑ k ∈ Finset.univ.erase i,
        (dominantSingletonProfile w i j k : ℝ) ^ 2 =
      ((dominantRemainderFinWeights w i j).natAbs : ℝ) ^ 2 := by
  have hsum := dominantSingletonProfile_sq_sum w i j
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
  have hiSq : (dominantSingletonProfile w i j i : ℝ) ^ 2 =
      (dominantAmplitude w i : ℝ) ^ 2 := by
    rw [dominantSingletonProfile_at_i]
    dsimp [dominantAmplitude]
    have habs : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs, sq_abs]
  rw [hiSq] at hsum
  linarith

/-- Quantitative normalized properties of the retained two-coordinate profile. -/
theorem dominantSingletonProfile_quantitative {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (j : Fin (Fintype.card (DominantRemainderIndex i)))
    (hi : w i ≠ 0)
    (hmax : ∀ k, (w k).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hlarge : 13 * dominantAmplitude w i <
      16 * (dominantRemainderFinWeights w i j).natAbs) :
    let compact := dominantSingletonProfile w i j
    let A := dominantAmplitude w i
    |(compact i : ℝ) / (A : ℝ)| = 1 ∧
      (∀ k, |(compact k : ℝ) / (A : ℝ)| ≤ 1) ∧
      (3 / 2 : ℝ) ≤ ∑ k, ((compact k : ℝ) / (A : ℝ)) ^ 2 ∧
      (169 / 256 : ℝ) ≤ ∑ k ∈ Finset.univ.erase i,
        ((compact k : ℝ) / (A : ℝ)) ^ 2 := by
  dsimp only
  let compact := dominantSingletonProfile w i j
  let A := dominantAmplitude w i
  let C := (dominantRemainderFinWeights w i j).natAbs
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hlargeReal : (13 : ℝ) * A < 16 * C := by exact_mod_cast hlarge
  have hCnonneg : (0 : ℝ) ≤ C := by positivity
  have hmassLower : (169 : ℝ) * A ^ 2 < 256 * C ^ 2 := by
    nlinarith
  have hunit : |(compact i : ℝ) / (A : ℝ)| = 1 := by
    rw [abs_div, abs_of_pos hAreal]
    have habs : |(compact i : ℝ)| = (A : ℝ) := by
      rw [show compact i = w i by simp [compact]]
      dsimp [A, dominantAmplitude]
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs, div_self hAreal.ne']
  have hcoordOne : ∀ k, |(compact k : ℝ) / (A : ℝ)| ≤ 1 := by
    intro k
    rw [abs_div, abs_of_pos hAreal, div_le_one hAreal]
    by_cases hk : k ∈ dominantLiftSupport i ({j} : Finset _)
    · rw [show compact k = w k by simp [compact, dominantSingletonProfile, hk]]
      have hnatReal : ((w k).natAbs : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 := by
        exact_mod_cast hmax k
      have habs : ((w k).natAbs : ℝ) = |(w k : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [habs] at hnatReal
      nlinarith [abs_nonneg (w k : ℝ)]
    · simp [compact, dominantSingletonProfile, hk, hAreal.le]
  have hsum := dominantSingletonProfile_sq_sum w i j
  have herase := dominantSingletonProfile_erase_sq_sum w i j
  have hmassFull : (3 / 2 : ℝ) ≤
      ∑ k, ((compact k : ℝ) / (A : ℝ)) ^ 2 := by
    rw [show (∑ k, ((compact k : ℝ) / (A : ℝ)) ^ 2) =
        ((A : ℝ) ^ 2 + C ^ 2) / (A : ℝ) ^ 2 by
      rw [← hsum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [div_pow]]
    apply (le_div_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  have hmassResidual : (169 / 256 : ℝ) ≤
      ∑ k ∈ Finset.univ.erase i,
        ((compact k : ℝ) / (A : ℝ)) ^ 2 := by
    rw [show (∑ k ∈ Finset.univ.erase i,
        ((compact k : ℝ) / (A : ℝ)) ^ 2) =
          (C : ℝ) ^ 2 / (A : ℝ) ^ 2 by
      rw [← herase, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [div_pow]]
    apply (le_div_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  exact ⟨hunit, hcoordOne, hmassFull, hmassResidual⟩

/-- Selective-Fourier transport for a large singleton below normalized
modulus `5/2`. -/
theorem sparseRow_centeredGaussian_le_dominantSingletonLowFourierRow
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (j : Fin (Fintype.card (DominantRemainderIndex i))) {z : ℝ}
    (hq : Odd q) (hi : w i ≠ 0) (hz : 0 < z)
    (hB : 2 < (q : ℝ) / (dominantAmplitude w i : ℝ))
    (hmax : ∀ k, (w k).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hlarge : 13 * dominantAmplitude w i <
      16 * (dominantRemainderFinWeights w i j).natAbs) :
    (∫ row, Real.exp (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
        sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantSingletonLowFourierRow
        ((q : ℝ) / (dominantAmplitude w i : ℝ)) z := by
  let A := dominantAmplitude w i
  let compact := dominantSingletonProfile w i j
  have hA : 0 < A := dominantAmplitude_pos hi
  have hproperties := dominantSingletonProfile_quantitative
    w i j hi hmax hlarge
  change |(compact i : ℝ) / (A : ℝ)| = 1 ∧
      (∀ k, |(compact k : ℝ) / (A : ℝ)| ≤ 1) ∧
      (3 / 2 : ℝ) ≤ ∑ k, ((compact k : ℝ) / (A : ℝ)) ^ 2 ∧
      (169 / 256 : ℝ) ≤ ∑ k ∈ Finset.univ.erase i,
        ((compact k : ℝ) / (A : ℝ)) ^ 2 at hproperties
  have htransport := sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict
    w (dominantLiftSupport i ({j} : Finset _)) hq
      (by positivity : 0 < z / (A : ℝ) ^ 2)
  have hwrapped :=
    sparseRow_wrappedGaussianKernel_le_dominantSingletonLowTwoMode
      A compact hq.pos hA hz hB hproperties.2.1 hproperties.2.2.1
  exact htransport.trans (by
    simpa only [compact, dominantSingletonProfile, A] using hwrapped)

/-- Selective-Fourier transport for a large singleton below normalized
modulus `5/2`, retaining the unit dominant-coordinate second-mode phase. -/
theorem sparseRow_centeredGaussian_le_dominantSingletonPhaseFourierRow
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (j : Fin (Fintype.card (DominantRemainderIndex i))) {z : ℝ}
    (hq : Odd q) (hi : w i ≠ 0) (hz : 0 < z)
    (hB : 2 < (q : ℝ) / (dominantAmplitude w i : ℝ))
    (hmax : ∀ k, (w k).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hlarge : 13 * dominantAmplitude w i <
      16 * (dominantRemainderFinWeights w i j).natAbs) :
    (∫ row, Real.exp (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
        sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantSingletonPhaseFourierRow
        ((q : ℝ) / (dominantAmplitude w i : ℝ)) z := by
  let A := dominantAmplitude w i
  let compact := dominantSingletonProfile w i j
  have hA : 0 < A := dominantAmplitude_pos hi
  have hproperties := dominantSingletonProfile_quantitative
    w i j hi hmax hlarge
  change |(compact i : ℝ) / (A : ℝ)| = 1 ∧
      (∀ k, |(compact k : ℝ) / (A : ℝ)| ≤ 1) ∧
      (3 / 2 : ℝ) ≤ ∑ k, ((compact k : ℝ) / (A : ℝ)) ^ 2 ∧
      (169 / 256 : ℝ) ≤ ∑ k ∈ Finset.univ.erase i,
        ((compact k : ℝ) / (A : ℝ)) ^ 2 at hproperties
  have htransport := sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict
    w (dominantLiftSupport i ({j} : Finset _)) hq
      (by positivity : 0 < z / (A : ℝ) ^ 2)
  have hwrapped :=
    sparseRow_wrappedGaussianKernel_le_dominantSingletonPhaseTwoMode
      A compact i hq.pos hA hz hB hproperties.1 hproperties.2.1
        hproperties.2.2.1
  exact htransport.trans (by
    simpa only [compact, dominantSingletonProfile, A] using hwrapped)

/-- Above normalized modulus `5/2`, the same large singleton transports to
the common capped row envelope. -/
theorem sparseRow_centeredGaussian_le_dominantLargeSingletonFourierRow
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (j : Fin (Fintype.card (DominantRemainderIndex i))) {z : ℝ}
    (hq : Odd q) (hi : w i ≠ 0) (hz : 0 < z)
    (hB : 5 / 2 ≤ (q : ℝ) / (dominantAmplitude w i : ℝ))
    (hmax : ∀ k, (w k).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hlarge : 13 * dominantAmplitude w i <
      16 * (dominantRemainderFinWeights w i j).natAbs) :
    (∫ row, Real.exp (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
        sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure) ≤
      thresholdDominantCappedFourierRow
        ((q : ℝ) / (dominantAmplitude w i : ℝ)) z := by
  let A := dominantAmplitude w i
  let compact := dominantSingletonProfile w i j
  have hA : 0 < A := dominantAmplitude_pos hi
  have hproperties := dominantSingletonProfile_quantitative
    w i j hi hmax hlarge
  change |(compact i : ℝ) / (A : ℝ)| = 1 ∧
      (∀ k, |(compact k : ℝ) / (A : ℝ)| ≤ 1) ∧
      (3 / 2 : ℝ) ≤ ∑ k, ((compact k : ℝ) / (A : ℝ)) ^ 2 ∧
      (169 / 256 : ℝ) ≤ ∑ k ∈ Finset.univ.erase i,
        ((compact k : ℝ) / (A : ℝ)) ^ 2 at hproperties
  have htransport := sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict
    w (dominantLiftSupport i ({j} : Finset _)) hq
      (by positivity : 0 < z / (A : ℝ) ^ 2)
  have hwrapped :=
    sparseRow_wrappedGaussianKernel_le_dominantLargeSingletonTwoMode
      A compact i hq.pos hA hz hB hproperties.1 hproperties.2.1
        hproperties.2.2.1 hproperties.2.2.2
  exact htransport.trans (by
    simpa only [compact, dominantSingletonProfile, A] using hwrapped)

end CertifiedJL
