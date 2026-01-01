/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Model.Distributions.BalancedTernary.MGF
import CertifiedJL.Model.Vectors.SquaredNorm
import CertifiedJL.Probability.Finite.FailureBudget
import Mathlib.Tactic

/-!
# Finite-model mutation canaries

These examples exercise the nontrivial boundaries of the finite-model API. They are
producer-side tests: changing a centered interval, entry mass, row marginal,
independence law, or MGF factor breaks this module.
-/

open scoped BigOperators ENNReal Matrix

open ProbabilityTheory

namespace CertifiedJL

noncomputable example {ι : Type} [Fintype ι]
    (α : ι → Type) [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] :
    PMF ((i : ι) → α i) :=
  uniformPiPMF α

example : centeredMod 5 7 = 2 := by
  apply (centeredMod_eq_iff (q := 5) (by norm_num) 7 2).mpr
  constructor
  · decide
  · norm_num [centeredInterval]

example : centeredMod 5 8 = -2 := by
  apply (centeredMod_eq_iff (q := 5) (by norm_num) 8 (-2)).mpr
  constructor
  · decide
  · norm_num [centeredInterval]

example : |centeredMod 5 13| ≤ |(13 : ℤ)| := by
  exact abs_centeredMod_le 5 13

/-- Modulus zero is the unreduced integer model. -/
example : centeredMod 0 (-13) = -13 := rfl

/-- At the even half-modulus tie the representative may flip sign, but its
magnitude—the quantity used by every norm theorem—is unchanged. -/
example : (centeredMod 2 1).natAbs = 1 := by
  decide

example : sqNorm ![(3 : ℤ), -4] = 25 := by
  norm_num [sqNorm, Fin.sum_univ_two]

example :
    eventProbability (PMF.uniformOfFintype Bool) (fun b => b = true) =
      (2 : ℝ≥0∞)⁻¹ := by
  rw [eventProbability_eq_sum, Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply]

example :
    eventProbability
        ((PMF.uniformOfFintype Bool).map id) (fun b => b = true) =
      eventProbability
        ((PMF.uniformOfFintype Bool).map (fun b => !b))
          (fun b => b = false) := by
  apply eventProbability_map_congr
  intro b
  cases b <;> decide

example : failureTarget 2 = (2 : ℝ≥0∞)⁻¹ ^ 2 := rfl

example :
    ∫ b, (if b then (3 : ℝ) else 1)
      ∂(PMF.uniformOfFintype Bool).toMeasure = 2 := by
  rw [finitePMF_integral_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]

example : sparseEntryPMF 0 = (2 : ℝ≥0∞)⁻¹ :=
  sparseEntryPMF_zero

noncomputable example
    {ι : Type} [Fintype ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    {β : ι → Type} [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)]
    [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSingletonClass (β i)]
    (f : (i : ι) → α i → β i)
    (hf : ∀ i, Measurable (f i)) (y : (i : ι) → β i) :
    uniformPiMap f y =
      ∏ i, ((PMF.uniformOfFintype (α i)).map (f i)) (y i) :=
  uniformPiMap_apply f hf y

example (m d : ℕ) :
    sparseRademacherMatrix m d =
      (PMF.uniformOfFintype (SparseSeed m d)).map sparseMatrix :=
  sparseRademacherMatrix_eq_map_uniformSeed m d

example (J : Matrix (Fin 2) (Fin 2) ℤ) (w : Fin 2 → ℤ) :
    (rowDot J w 1 : ℝ) =
      realRowDot (J 1) (fun i => (w i : ℝ)) :=
  intRowDot_cast_eq_realRowDot J w 1

example (a b : ℝ) :
    ∫ row, Real.exp (realRowDot row ![a, b]) ∂(sparseRademacherRow 2).toMeasure =
      ((1 + Real.cosh a) / 2) * ((1 + Real.cosh b) / 2) := by
  rw [sparseRowMGF]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

end CertifiedJL
