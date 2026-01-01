/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap42Diffuse.FourierBridge
import CertifiedJL.Probability.Finite.IidQuadratic

/-!
# Mutation canaries for the two-decimal ternary `L∞` Fourier bridge

These tests hold one side of the generated Fourier-to-power equality fixed and
perturb the other.  They guard the semantic boundary against a checker that
accidentally ignores either source Fourier data or padded power coefficients.
-/

open CertifiedJL.TrigonometricBernstein
open MeasureTheory

namespace CertifiedJL.Tests.TernaryLInfTwoDecimalFourierBridge

open TernaryLInfTwoDecimal.Cap42Diffuse

def perturbHead : List ℚ → List ℚ
  | [] => [1]
  | coefficient :: coefficients => (coefficient + 1) :: coefficients

def perturbLast : List ℚ → List ℚ
  | [] => [1]
  | [coefficient] => [coefficient + 1]
  | coefficient :: coefficients => coefficient :: perturbLast coefficients

set_option maxHeartbeats 40000000 in
-- This recomputes the full degree-73 conversion after mutating the Fourier side.
set_option maxRecDepth 1000000 in
example : chebyshevCombinationPower (perturbHead fourier) ≠ power := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- The last cap-0.42 diffuse power entry is padding and must still be checked.
set_option maxRecDepth 1000000 in
example : chebyshevCombinationPower fourier ≠ perturbLast power := by
  decide +kernel

example :
    nonpositiveBlockCheck (fourier.set 3 1) 2 (degree + 1 - 2) = false := by
  decide +kernel

example : ¬(fourier.getD 0 0 + fourier.getD 1 0 * diffuseMomentBound ≤
    expectationBound - 1) := by
  decide +kernel

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (phase : Ω → ℝ)
    (hintegrable : ∀ j : ℕ, Integrable
      (fun z => Real.cos ((j : ℝ) * phase z)) μ) :
    (∫ z, rationalCosineValue [2, 3, 4] (phase z) ∂μ) =
      2 * (∫ z, Real.cos ((0 : ℝ) * phase z) ∂μ) +
      3 * (∫ z, Real.cos ((1 : ℝ) * phase z) ∂μ) +
      4 * (∫ z, Real.cos ((2 : ℝ) * phase z) ∂μ) := by
  rw [integral_rationalCosineValue μ [2, 3, 4] phase hintegrable]
  simp [rationalFourierExpectation, rationalFourierExpectationFrom]
  ring

example {Ω : Type*} [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : PMF Ω) (phase : Ω → ℝ)
    (hmomentNonnegative : ∀ j : ℕ,
      0 ≤ ∫ z, Real.cos ((j : ℝ) * phase z) ∂p.toMeasure)
    (hmomentOne : (∫ z, Real.cos ((1 : ℝ) * phase z) ∂p.toMeasure) ≤
      (diffuseMomentBound : ℝ)) :
    (∫ z, rationalCosineValue fourier (phase z) ∂p.toMeasure) ≤
      (expectationBound : ℝ) := by
  apply integral_rationalCosineValue_le_of_diffuseContract p.toMeasure phase
    fourierContract
  · intro j
    exact CertifiedJL.integrable_of_finitePMF p _
  · simp
  · exact hmomentNonnegative
  · exact hmomentOne

end CertifiedJL.Tests.TernaryLInfTwoDecimalFourierBridge
