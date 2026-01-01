/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Finite.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Local analytic soundness of the sparse one-row scalar certificate

The executable shards prove that every rational cell endpoint is below the
strict target.  This module connects those Boolean facts to the real scalar
envelope `(O9)` by proving:

1. every real endpoint expression is contained in its computed interval;
2. the endpoint expression dominates the scalar envelope throughout its
   cell; and
3. the retained prefix supplies the strict check throughout `[0,32/125]`.
-/

open scoped BigOperators

namespace CertifiedJL
namespace SparseOneRowCertificate

/-- The real scalar envelope `(O9)` evaluated at `y`. -/
noncomputable def scalarEnvelope (y : ℝ) : ℝ :=
  Real.exp (-(exponentRate : ℝ) * (1 + y ^ 2)) *
    Real.cosh ((xUpper : ℝ) * y) *
      ((gaussianCoefficientUpper : ℝ) *
          Real.cosh ((xUpper : ℝ) * y ^ 2) +
        (berryEsseenFactor : ℝ) * y ^ 2 *
          Real.cosh ((xUpper : ℝ) * y ^ 2) ^ 3)

/-- The monotone real upper endpoint used for one certificate cell. -/
noncomputable def cellEnvelope (index : ℕ) : ℝ :=
  let left : ℝ := cellLeftRat index
  let right : ℝ := cellRightRat index
  Real.exp (-(exponentRate : ℝ) * (1 + left ^ 2)) *
    Real.cosh ((xUpper : ℝ) * right) *
      ((gaussianCoefficientUpper : ℝ) *
          Real.cosh ((xUpper : ℝ) * right ^ 2) +
        (berryEsseenFactor : ℝ) * right ^ 2 *
          Real.cosh ((xUpper : ℝ) * right ^ 2) ^ 3)

theorem xUpper_nonneg : (0 : ℚ) ≤ xUpper := by
  norm_num [xUpper]

theorem gaussianCoefficientUpper_nonneg :
    (0 : ℚ) ≤ gaussianCoefficientUpper := by
  norm_num [gaussianCoefficientUpper]

theorem berryEsseenFactor_nonneg :
    (0 : ℚ) ≤ berryEsseenFactor := by
  norm_num [berryEsseenFactor]

theorem exponentRate_nonneg : (0 : ℚ) ≤ exponentRate := by
  norm_num [exponentRate]

/--
Every nonnegative argument below `xUpper` satisfies the side conditions of
the certified hyperbolic-cosine evaluator.
-/
theorem coshUpper_contains_of_le_xUpper {q : ℚ}
    (hq0 : 0 ≤ q) (hq : q ≤ xUpper) :
    (coshUpper q).Contains (Real.cosh q) := by
  apply Cosh.upper_contains hq0
  · exact hq.trans_lt (by norm_num [xUpper, squarings])
  · apply Dyadic.roundDown_pos
    have hhalf :
        (1 / 2 : ℚ) ≤ 1 - q / (2 ^ squarings : ℕ) := by
      have hq' : q ≤ (2 ^ squarings : ℕ) / 2 := by
        exact hq.trans (by norm_num [xUpper, squarings])
      have hdenom :
          (0 : ℚ) < (2 ^ squarings : ℕ) := by positivity
      have hquot :
          q / (2 ^ squarings : ℕ) ≤ (1 / 2 : ℚ) := by
        rw [div_le_iff₀ hdenom]
        nlinarith
      linarith
    calc
      (1 : ℚ) ≤ (1 / 2 : ℚ) * Dyadic.scale precision := by
        norm_num [Dyadic.scale, precision]
      _ ≤ (1 - q / (2 ^ squarings : ℕ)) *
          Dyadic.scale precision :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)

/-- The right endpoint of every committed cell lies in `[0,1]`. -/
theorem cellRightRat_mem_unit {index : ℕ} (hindex : index < gridSize) :
    (0 : ℚ) ≤ cellRightRat index ∧ cellRightRat index ≤ 1 := by
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · rw [cellRightRat, div_le_one
      (by norm_num [gridDenominator] : (0 : ℚ) < gridDenominator)]
    have hle : index + 1 ≤ gridSize := Nat.add_one_le_iff.mpr hindex
    exact_mod_cast hle.trans (by norm_num [gridSize, gridDenominator])

/-- The left endpoint is nonnegative and no larger than the right endpoint. -/
theorem cellLeftRat_le_rightRat (index : ℕ) :
    (0 : ℚ) ≤ cellLeftRat index ∧
      cellLeftRat index ≤ cellRightRat index := by
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · unfold cellLeftRat cellRightRat
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Nat.le_add_right index 1
    · norm_num [gridDenominator]

/-- `cosh (c * ·)` is monotone on the nonnegative axis when `c ≥ 0`. -/
theorem cosh_mul_le_cosh_mul {c u v : ℝ}
    (hc : 0 ≤ c) (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.cosh (c * u) ≤ Real.cosh (c * v) := by
  rw [Real.cosh_le_cosh]
  have hv : 0 ≤ v := hu.trans huv
  rw [abs_of_nonneg (mul_nonneg hc hu),
    abs_of_nonneg (mul_nonneg hc hv)]
  exact mul_le_mul_of_nonneg_left huv hc

/--
The endpoint expression dominates the scalar envelope throughout its cell.
-/
theorem scalarEnvelope_le_cellEnvelope
    {index : ℕ} {y : ℝ}
    (hcell :
      (cellLeftRat index : ℝ) ≤ y ∧
        y ≤ (cellRightRat index : ℝ))
    (hindex : index < gridSize) :
    scalarEnvelope y ≤ cellEnvelope index := by
  let left : ℝ := cellLeftRat index
  let right : ℝ := cellRightRat index
  have hleftRat := cellLeftRat_le_rightRat index
  have hrightRat := cellRightRat_mem_unit hindex
  have hleft0 : 0 ≤ left := by
    change (0 : ℝ) ≤ (cellLeftRat index : ℝ)
    exact_mod_cast hleftRat.1
  have hright0 : 0 ≤ right := by
    change (0 : ℝ) ≤ (cellRightRat index : ℝ)
    exact_mod_cast hrightRat.1
  have hy0 : 0 ≤ y := hleft0.trans hcell.1
  have hleftSquare : left ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hleft0 hy0).mpr hcell.1
  have hrightSquare : y ^ 2 ≤ right ^ 2 :=
    (sq_le_sq₀ hy0 hright0).mpr hcell.2
  have hx0 : (0 : ℝ) ≤ xUpper := by
    exact_mod_cast xUpper_nonneg
  have hrate0 : (0 : ℝ) ≤ exponentRate := by
    exact_mod_cast exponentRate_nonneg
  have hgaussian0 : (0 : ℝ) ≤ gaussianCoefficientUpper := by
    exact_mod_cast gaussianCoefficientUpper_nonneg
  have hberry0 : (0 : ℝ) ≤ berryEsseenFactor := by
    exact_mod_cast berryEsseenFactor_nonneg
  have hexp :
      Real.exp (-(exponentRate : ℝ) * (1 + y ^ 2)) ≤
        Real.exp (-(exponentRate : ℝ) * (1 + left ^ 2)) := by
    rw [Real.exp_le_exp]
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hrate0)
    linarith
  have hcoshLinear :
      Real.cosh ((xUpper : ℝ) * y) ≤
        Real.cosh ((xUpper : ℝ) * right) :=
    cosh_mul_le_cosh_mul hx0 hy0 hcell.2
  have hcoshQuadratic :
      Real.cosh ((xUpper : ℝ) * y ^ 2) ≤
        Real.cosh ((xUpper : ℝ) * right ^ 2) :=
    cosh_mul_le_cosh_mul hx0 (sq_nonneg y) hrightSquare
  have hcoshCube :
      Real.cosh ((xUpper : ℝ) * y ^ 2) ^ 3 ≤
        Real.cosh ((xUpper : ℝ) * right ^ 2) ^ 3 :=
    pow_le_pow_left₀ (Real.cosh_pos _).le hcoshQuadratic 3
  have hfirst :
      (gaussianCoefficientUpper : ℝ) *
          Real.cosh ((xUpper : ℝ) * y ^ 2) ≤
        (gaussianCoefficientUpper : ℝ) *
          Real.cosh ((xUpper : ℝ) * right ^ 2) :=
    mul_le_mul_of_nonneg_left hcoshQuadratic hgaussian0
  have hsecond :
      (berryEsseenFactor : ℝ) * y ^ 2 *
          Real.cosh ((xUpper : ℝ) * y ^ 2) ^ 3 ≤
        (berryEsseenFactor : ℝ) * right ^ 2 *
          Real.cosh ((xUpper : ℝ) * right ^ 2) ^ 3 := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hrightSquare hberry0)
      hcoshCube
      (pow_nonneg (Real.cosh_pos _).le 3)
      (mul_nonneg hberry0 (sq_nonneg right))
  have hbracket :
      (gaussianCoefficientUpper : ℝ) *
            Real.cosh ((xUpper : ℝ) * y ^ 2) +
          (berryEsseenFactor : ℝ) * y ^ 2 *
            Real.cosh ((xUpper : ℝ) * y ^ 2) ^ 3 ≤
        (gaussianCoefficientUpper : ℝ) *
            Real.cosh ((xUpper : ℝ) * right ^ 2) +
          (berryEsseenFactor : ℝ) * right ^ 2 *
            Real.cosh ((xUpper : ℝ) * right ^ 2) ^ 3 :=
    add_le_add hfirst hsecond
  have hbracketNonneg :
      0 ≤
        (gaussianCoefficientUpper : ℝ) *
            Real.cosh ((xUpper : ℝ) * y ^ 2) +
          (berryEsseenFactor : ℝ) * y ^ 2 *
            Real.cosh ((xUpper : ℝ) * y ^ 2) ^ 3 :=
    add_nonneg
      (mul_nonneg hgaussian0 (Real.cosh_pos _).le)
      (mul_nonneg
        (mul_nonneg hberry0 (sq_nonneg y))
        (pow_nonneg (Real.cosh_pos _).le 3))
  have hmiddle :
      Real.exp (-(exponentRate : ℝ) * (1 + y ^ 2)) *
          Real.cosh ((xUpper : ℝ) * y) ≤
        Real.exp (-(exponentRate : ℝ) * (1 + left ^ 2)) *
          Real.cosh ((xUpper : ℝ) * right) :=
    mul_le_mul hexp hcoshLinear
      (Real.cosh_pos _).le (Real.exp_nonneg _)
  unfold scalarEnvelope cellEnvelope
  dsimp only [left, right]
  exact mul_le_mul hmiddle hbracket hbracketNonneg
    (mul_nonneg (Real.exp_nonneg _) (Real.cosh_pos _).le)

/-- The computed interval encloses the real monotone endpoint expression. -/
theorem cellUpper_contains_cellEnvelope
    {index : ℕ} (hindex : index < gridSize) :
    (cellUpper index).Contains (cellEnvelope index) := by
  let left : ℚ := cellLeftRat index
  let right : ℚ := cellRightRat index
  have hleft := cellLeftRat_le_rightRat index
  have hright := cellRightRat_mem_unit hindex
  have hrightSquare : (0 : ℚ) ≤ right * right :=
    mul_nonneg hright.1 hright.1
  have hlinearLe : xUpper * right ≤ xUpper := by
    nlinarith [xUpper_nonneg]
  have hquadraticLe : xUpper * (right * right) ≤ xUpper := by
    have hsquareLe : right * right ≤ 1 := by nlinarith
    nlinarith [xUpper_nonneg]
  have hexp :
      (Exp.negUpper precision
        (exponentRate * (1 + left * left)) squarings).Contains
        (Real.exp (-(exponentRate * (1 + left * left) : ℚ))) := by
    apply Exp.negUpper_contains
    exact mul_nonneg exponentRate_nonneg
      (by nlinarith [hleft.1])
  have hcoshLinear :
      (coshUpper (xUpper * right)).Contains
        (Real.cosh (xUpper * right : ℚ)) :=
    coshUpper_contains_of_le_xUpper
      (mul_nonneg xUpper_nonneg hright.1) hlinearLe
  have hcoshQuadratic :
      (coshUpper (xUpper * (right * right))).Contains
        (Real.cosh (xUpper * (right * right) : ℚ)) :=
    coshUpper_contains_of_le_xUpper
      (mul_nonneg xUpper_nonneg hrightSquare) hquadraticLe
  have hgaussian :
      (ratInterval gaussianCoefficientUpper).Contains
        (gaussianCoefficientUpper : ℝ) :=
    Interval.contains_ofRat precision gaussianCoefficientUpper
  have hberry :
      (ratInterval berryEsseenFactor).Contains
        (berryEsseenFactor : ℝ) :=
    Interval.contains_ofRat precision berryEsseenFactor
  have hrightSquareInterval :
      (ratInterval (right * right)).Contains ((right * right : ℚ) : ℝ) :=
    Interval.contains_ofRat precision (right * right)
  have hcoshCube :
      (coshUpper (xUpper * (right * right)) *
          coshUpper (xUpper * (right * right)) *
          coshUpper (xUpper * (right * right))).Contains
        (Real.cosh (xUpper * (right * right) : ℚ) ^ 3) := by
    have hmul := Interval.contains_mul
      (Interval.contains_mul hcoshQuadratic hcoshQuadratic)
      hcoshQuadratic
    simpa [pow_succ] using hmul
  have hbracket :
      (ratInterval gaussianCoefficientUpper *
          coshUpper (xUpper * (right * right)) +
        ratInterval berryEsseenFactor * ratInterval (right * right) *
          (coshUpper (xUpper * (right * right)) *
            coshUpper (xUpper * (right * right)) *
            coshUpper (xUpper * (right * right)))).Contains
        ((gaussianCoefficientUpper : ℝ) *
            Real.cosh (xUpper * (right * right) : ℚ) +
          (berryEsseenFactor : ℝ) * (right * right : ℚ) *
            Real.cosh (xUpper * (right * right) : ℚ) ^ 3) := by
    exact Interval.contains_add
      (Interval.contains_mul hgaussian hcoshQuadratic)
      (Interval.contains_mul
        (Interval.contains_mul hberry hrightSquareInterval)
        hcoshCube)
  have htotal :=
    Interval.contains_mul (Interval.contains_mul hexp hcoshLinear) hbracket
  simpa only [cellUpper, cellEnvelope, left, right, pow_two, mul_pow, neg_mul,
    Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_neg] using htotal

/-- A checked endpoint proves the real scalar envelope on its cell. -/
theorem scalarEnvelope_lt_target_of_cellCheck
    {index : ℕ} {y : ℝ}
    (hcell :
      (cellLeftRat index : ℝ) ≤ y ∧
        y ≤ (cellRightRat index : ℝ))
    (hindex : index < gridSize)
    (hcheck : cellCheck index = true) :
    scalarEnvelope y < (target : ℝ) := by
  exact (scalarEnvelope_le_cellEnvelope hcell hindex).trans_lt <|
    Interval.lt_of_contains_of_upperLTCheck
      (cellUpper_contains_cellEnvelope hindex) hcheck

/-- Every point of `[0,32/125]` belongs to one of the retained rational cells. -/
theorem exists_certificate_cell_of_le_certifiedProfileUpper {y : ℝ}
    (hy0 : 0 ≤ y) (hy : y ≤ (certifiedProfileUpper : ℝ)) :
    ∃ index < gridSize,
      (cellLeftRat index : ℝ) ≤ y ∧
        y ≤ (cellRightRat index : ℝ) := by
  let index : ℕ := ⌊(gridDenominator : ℝ) * y⌋₊
  have hdenomPos : (0 : ℝ) < gridDenominator := by
    norm_num [gridDenominator]
  have hscaled0 : 0 ≤ (gridDenominator : ℝ) * y :=
    mul_nonneg hdenomPos.le hy0
  have hscaledLt : (gridDenominator : ℝ) * y < gridSize := by
    calc
      (gridDenominator : ℝ) * y ≤
          (gridDenominator : ℝ) * certifiedProfileUpper :=
        mul_le_mul_of_nonneg_left hy hdenomPos.le
      _ < gridSize := by
        norm_num [gridDenominator, certifiedProfileUpper, gridSize]
  have hindex : index < gridSize := by
    exact (Nat.floor_lt' (by norm_num [gridSize])).2 hscaledLt
  refine ⟨index, hindex, ?_⟩
  constructor
  · simp only [cellLeftRat, Rat.cast_div, Rat.cast_natCast]
    rw [div_le_iff₀ hdenomPos]
    simpa [index, mul_comm] using Nat.floor_le hscaled0
  · simp only [cellRightRat, Rat.cast_div, Rat.cast_natCast]
    rw [le_div_iff₀ hdenomPos]
    simpa [index, mul_comm, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((gridDenominator : ℝ) * y)).le

end SparseOneRowCertificate
end CertifiedJL
