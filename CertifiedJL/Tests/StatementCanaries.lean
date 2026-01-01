/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Projection.Counterexamples.L2Upper.Statements
import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.L2.Upper.Rows256Bits128
import CertifiedJL.Statements.LInf.Lower.Affine
import CertifiedJL.Statements.LInf.Upper
import CertifiedJL.Statements.OneRow.Endpoint975
import Mathlib.Tactic

/-!
# Statement mutation canaries

These small theorems fail when a headline constant, event strictness, entry
distribution, or centered-reduction convention changes accidentally. A successful
canary build is not an attestation of the complete registered certificate
closure; replay status is recorded separately in the evidence catalogs.
-/

namespace CertifiedJL

/-! The affine shift is fixed outside the random-matrix event. -/

example (parameters : L2ThresholdLowerParameters) (budget : ENNReal) :
    AffineL2ThresholdLowerTailAt parameters budget ↔
      ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ)
          (shift : Fin parameters.rows → ℤ),
        Odd q →
        CenteredInput q w →
        0 < inputThreshold →
        InputThresholdAtMostNorm inputThreshold w →
        InputThresholdWithinModulus parameters.modulusMargin q inputThreshold →
        eventProbability (parameters.distribution.matrixPMF parameters.rows d)
          (AffineL2ThresholdLowerFailure parameters.squaredNormFloor
            inputThreshold q shift w) < budget :=
  Iff.rfl

example (q inputThreshold : ℕ) {d : ℕ} (shift : Fin 256 → ℤ)
    (w : Fin d → ℤ) (J : Fin 256 → Fin d → ℤ) :
    AffineL2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
        inputThreshold q shift w J ↔
      shiftedModularProjectionSqNorm q shift J w < 29 * inputThreshold ^ 2 := by
  simp [AffineL2ThresholdLowerFailure, NonnegativeRatio.ofNat]

example : securityBits = 128 := rfl
example : rowCount = 256 := rfl

example : sparseUpperThreshold = 338 := rfl

example :
    SparseUpper338Bits130CounterexampleStatement ↔
      let w := sparseUpperCounterexampleVector
      Odd counterexampleModulus ∧
        w ≠ 0 ∧
        eventProbability
            (sparseRademacherMatrix rowCount counterexampleDimension)
            (fun J =>
              modularProjectionSqNorm counterexampleModulus J w >
                338 * sqNorm w) >
            ((3 : ENNReal) / 2) * failureTarget 130 := by
  rfl

example : sparseOneRowSecurityBits = 141 := rfl

example :
    SparseOneRow975Statement ↔
      ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)),
        eventProbability (sparseRademacherRow d) (SparseOneRow975Event w) <
          failureTarget 141 := by
  rfl

example {d : ℕ} (row : Fin d → ℤ) :
    ¬SparseOneRow975Event (0 : EuclideanSpace ℝ (Fin d)) row := by
  simp [SparseOneRow975Event]

example (w : EuclideanSpace ℝ (Fin 0)) (row : Fin 0 → ℤ) :
    ¬SparseOneRow975Event w row := by
  have hw : w = 0 := Subsingleton.elim _ _
  subst w
  simp [SparseOneRow975Event]

example : sparseOneRowRademacherThreshold =
    (39 / 4 : ℝ) * Real.sqrt 2 := rfl

/-! The infinity lower-tail schema is relative to a public threshold, not the
actual norm of the adversarial vector. The quantifier below deliberately uses
positive natural thresholds and odd moduli; a real-threshold application needs
an adapter. Its closed infinity event does not change the strict L2 schema. -/

example :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 130) ↔
    ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
      Odd q →
      (∀ i, w i ∈ centeredInterval q) →
      0 < inputThreshold →
      inputThreshold ^ 2 ≤ sqNorm w →
      2 * inputThreshold ≤ q →
      eventProbability (sparseRademacherMatrix 256 d)
        (LInfThresholdSmallProjection
          { distribution := .balancedTernary
            rows := 256
            coordinateCap :=
              { numerator := 21, denominator := 50, denominator_pos := by decide }
            modulusMargin := NonnegativeRatio.ofNat 2 }
          inputThreshold q w) < failureTarget 130 := by
  simp [LInfThresholdLowerTailAt, CenteredInput,
    InputThresholdAtMostNorm, InputThresholdWithinModulus,
    NonnegativeRatio.ofNat]

example (q inputThreshold : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (J : Fin 256 → Fin d → ℤ) :
    LInfThresholdSmallProjection
        { distribution := .balancedTernary
          rows := 256
          coordinateCap :=
            { numerator := 21, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        inputThreshold q w J ↔
      ∀ j, 2500 * (centeredMod q (rowDot J w j)).natAbs ^ 2 ≤
        441 * inputThreshold ^ 2 := by
  simp [LInfThresholdSmallProjection]

/-! The infinity upper-tail schema is a matrix event relative to the actual
Euclidean norm. Centered reduction is part of the event, but its hypotheses do
not impose a modulus-to-norm relation. -/

example :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateThreshold :=
          { numerator := 1181, denominator := 100,
            denominator_pos := by decide } }
      (failureTarget 192) ↔
    ∀ (q d : ℕ) (w : Fin d → ℤ),
      eventProbability (sparseRademacherMatrix 256 d)
        (LInfUpperFailure
          { distribution := .balancedTernary
            rows := 256
            coordinateThreshold :=
              { numerator := 1181, denominator := 100,
                denominator_pos := by decide } }
          q w) <
        failureTarget 192 := by
  rfl

example (q : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (J : Fin 256 → Fin d → ℤ) :
    LInfUpperFailure
        { distribution := .balancedTernary
          rows := 256
          coordinateThreshold :=
            { numerator := 1181, denominator := 100,
              denominator_pos := by decide } }
        q w J ↔
      ∃ j, 1181 ^ 2 * sqNorm w <
        100 ^ 2 * (centeredMod q (rowDot J w j)).natAbs ^ 2 := by
  simp [LInfUpperFailure]

example : signBit false = -1 := rfl
example : signBit true = 1 := rfl

example : sparseBit (false, false) = -1 := rfl
example : sparseBit (false, true) = 0 := rfl
example : sparseBit (true, false) = 0 := rfl
example : sparseBit (true, true) = 1 := rfl

example : centeredMod 5 2 = 2 := by
  exact centeredMod_eq_self (by norm_num) (by norm_num [centeredInterval])

example : centeredMod 5 3 = -2 := by
  apply (centeredMod_eq_iff (q := 5) (by norm_num) 3 (-2)).mpr
  constructor
  · decide
  · norm_num [centeredInterval]

example : centeredMod 5 (-3) = 2 := by
  apply (centeredMod_eq_iff (q := 5) (by norm_num) (-3) 2).mpr
  constructor
  · decide
  · norm_num [centeredInterval]

example (q : ℕ) {m d : ℕ} (w : Fin d → ℤ)
    (J : Matrix (Fin m) (Fin d) ℤ) :
    SparseUpperFailure q w J ↔
      modularProjectionSqNorm q J w > 338 * sqNorm w := Iff.rfl

example :
    SparseUpper128Statement ↔
      ∀ (q d : ℕ) (w : Fin d → ℤ),
        eventProbability (sparseRademacherMatrix 256 d)
          (fun J => modularProjectionSqNorm q J w > 338 * sqNorm w) <
            (2 : ENNReal)⁻¹ ^ 128 := by
  rfl

/-! The following exact boundary profile detects `>` being weakened to `≥`. -/

private noncomputable def boundaryT : ℝ := 4 * Real.sqrt 5 / 13

private noncomputable def boundaryW : EuclideanSpace ℝ (Fin 96) :=
  WithLp.toLp 2 (fun i : Fin 96 =>
    if i = 0 then 1 + boundaryT
    else if i = 1 then 1 - boundaryT
    else 1)

private def boundaryRow : Fin 96 → ℤ := fun _ => 1

private theorem boundary_dot :
    euclideanRowDot boundaryRow boundaryW = 96 := by
  simp [euclideanRowDot, realRowDot, boundaryRow, boundaryW, boundaryT,
    Fin.sum_univ_succ]
  all_goals ring

private theorem boundary_norm :
    ‖boundaryW‖ = (128 : ℝ) / 13 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsq : ‖boundaryW‖ ^ 2 = ((128 : ℝ) / 13) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [boundaryW, boundaryT, Fin.sum_univ_succ]
    field_simp
    nlinarith
  nlinarith [norm_nonneg boundaryW]

example :
    |euclideanRowDot boundaryRow boundaryW| =
      ((39 : ℝ) / 4) * ‖boundaryW‖ := by
  rw [boundary_dot, boundary_norm]
  norm_num

example : ¬SparseOneRow975Event boundaryW boundaryRow := by
  simp only [SparseOneRow975Event, boundary_dot, boundary_norm]
  norm_num

end CertifiedJL
