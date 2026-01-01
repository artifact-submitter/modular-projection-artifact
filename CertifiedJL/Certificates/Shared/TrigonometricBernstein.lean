/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# Exact trigonometric-polynomial majorant certificates

This module is the small semantic soundness boundary used by the high-degree
balanced-ternary `L∞` lower-tail certificates.  Concrete generated modules
contain only rational coefficients and kernel-checked polynomial identities.
No external certificate is read during elaboration.
-/

open scoped BigOperators Polynomial
open MeasureTheory

namespace CertifiedJL
namespace TrigonometricBernstein

open Polynomial

/-- A rational power-basis polynomial.  Concrete certificates keep arithmetic
in `ℚ` and map the proved identity to `ℝ` only at the semantic boundary. -/
noncomputable def powerPolynomialQ (coefficients : List ℚ) : ℚ[X] :=
  ∑ j ∈ Finset.range coefficients.length,
    C (coefficients.getD j 0) * X ^ j

theorem powerPolynomialQ_coeff (coefficients : List ℚ) (k : ℕ) :
    (powerPolynomialQ coefficients).coeff k = coefficients.getD k 0 := by
  by_cases hk : k < coefficients.length
  · simp [powerPolynomialQ, hk]
  · simp [powerPolynomialQ, hk]

/-- Subtract a constant from a nonempty power-basis coefficient list. -/
def subtractConstant : List ℚ → ℚ → List ℚ
  | [], r => [-r]
  | c :: coefficients, r => (c - r) :: coefficients

theorem powerPolynomialQ_subtractConstant (c : ℚ) (coefficients : List ℚ) (r : ℚ) :
    powerPolynomialQ (subtractConstant (c :: coefficients) r) =
      powerPolynomialQ (c :: coefficients) - C r := by
  ext k
  rw [powerPolynomialQ_coeff, coeff_sub, powerPolynomialQ_coeff, coeff_C]
  cases k <;> simp [subtractConstant]

/-! ## Executable Chebyshev-to-power conversion -/

/-- Coefficientwise addition, retaining the longer input's trailing entries. -/
def addPowerCoefficients : List ℚ → List ℚ → List ℚ
  | [], right => right
  | left, [] => left
  | a :: left, b :: right => (a + b) :: addPowerCoefficients left right

theorem addPowerCoefficients_getD (left right : List ℚ) (k : ℕ) :
    (addPowerCoefficients left right).getD k 0 =
      left.getD k 0 + right.getD k 0 := by
  induction left generalizing right k with
  | nil => simp [addPowerCoefficients]
  | cons a left ih =>
      cases right with
      | nil => simp [addPowerCoefficients]
      | cons b right =>
          cases k with
          | zero => simp [addPowerCoefficients]
          | succ k => simpa [addPowerCoefficients] using ih right k

/-- Coefficientwise negation. -/
def negPowerCoefficients (coefficients : List ℚ) : List ℚ :=
  coefficients.map (-·)

theorem negPowerCoefficients_getD (coefficients : List ℚ) (k : ℕ) :
    (negPowerCoefficients coefficients).getD k 0 = -coefficients.getD k 0 := by
  simpa [negPowerCoefficients] using
    (List.getD_map (l := coefficients) (d := (0 : ℚ)) (n := k) (-·))

/-- Coefficientwise scalar multiplication. -/
def scalePowerCoefficients (q : ℚ) (coefficients : List ℚ) : List ℚ :=
  coefficients.map (q * ·)

theorem scalePowerCoefficients_getD (q : ℚ) (coefficients : List ℚ) (k : ℕ) :
    (scalePowerCoefficients q coefficients).getD k 0 =
      q * coefficients.getD k 0 := by
  simpa [scalePowerCoefficients] using
    (List.getD_map (l := coefficients) (d := (0 : ℚ)) (n := k) (q * ·))

/-- Multiply a power-basis coefficient list by `2X`. -/
def twiceXPowerCoefficients (coefficients : List ℚ) : List ℚ :=
  0 :: scalePowerCoefficients 2 coefficients

theorem powerPolynomialQ_addPowerCoefficients (left right : List ℚ) :
    powerPolynomialQ (addPowerCoefficients left right) =
      powerPolynomialQ left + powerPolynomialQ right := by
  ext k
  simp only [powerPolynomialQ_coeff, coeff_add]
  exact addPowerCoefficients_getD left right k

theorem powerPolynomialQ_negPowerCoefficients (coefficients : List ℚ) :
    powerPolynomialQ (negPowerCoefficients coefficients) =
      -powerPolynomialQ coefficients := by
  ext k
  simp only [powerPolynomialQ_coeff, coeff_neg]
  exact negPowerCoefficients_getD coefficients k

theorem powerPolynomialQ_scalePowerCoefficients (q : ℚ) (coefficients : List ℚ) :
    powerPolynomialQ (scalePowerCoefficients q coefficients) =
      C q * powerPolynomialQ coefficients := by
  ext k
  simp only [powerPolynomialQ_coeff, coeff_C_mul]
  exact scalePowerCoefficients_getD q coefficients k

theorem powerPolynomialQ_zero_cons (coefficients : List ℚ) :
    powerPolynomialQ (0 :: coefficients) = X * powerPolynomialQ coefficients := by
  ext k
  cases k with
  | zero => simp [powerPolynomialQ_coeff]
  | succ k =>
      rw [powerPolynomialQ_coeff, coeff_X_mul, powerPolynomialQ_coeff]
      simp

theorem powerPolynomialQ_singleton (q : ℚ) :
    powerPolynomialQ [q] = C q := by
  ext k
  cases k <;> simp [powerPolynomialQ_coeff]

theorem powerPolynomialQ_twiceXPowerCoefficients (coefficients : List ℚ) :
    powerPolynomialQ (twiceXPowerCoefficients coefficients) =
      2 * X * powerPolynomialQ coefficients := by
  rw [twiceXPowerCoefficients, powerPolynomialQ_zero_cons,
    powerPolynomialQ_scalePowerCoefficients]
  rw [C_ofNat]
  ring_nf

/-- Coefficientwise subtraction, retaining enough zero padding for either input. -/
def subPowerCoefficients (left right : List ℚ) : List ℚ :=
  addPowerCoefficients left (negPowerCoefficients right)

theorem powerPolynomialQ_subPowerCoefficients (left right : List ℚ) :
    powerPolynomialQ (subPowerCoefficients left right) =
      powerPolynomialQ left - powerPolynomialQ right := by
  rw [subPowerCoefficients, powerPolynomialQ_addPowerCoefficients,
    powerPolynomialQ_negPowerCoefficients, sub_eq_add_neg]

/-- The exact rational power coefficients of the `n`-th Chebyshev polynomial. -/
def chebyshevPowerCoefficients : ℕ → List ℚ
  | 0 => [1]
  | 1 => [0, 1]
  | n + 2 =>
      subPowerCoefficients
        (twiceXPowerCoefficients (chebyshevPowerCoefficients (n + 1)))
        (chebyshevPowerCoefficients n)

theorem powerPolynomialQ_chebyshevPowerCoefficients (n : ℕ) :
    powerPolynomialQ (chebyshevPowerCoefficients n) =
      Polynomial.Chebyshev.T ℚ (n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebyshevPowerCoefficients, powerPolynomialQ_singleton]
  | one =>
      rw [chebyshevPowerCoefficients, powerPolynomialQ_zero_cons,
        powerPolynomialQ_singleton]
      simp
  | more n ih0 ih1 =>
      rw [chebyshevPowerCoefficients, powerPolynomialQ_subPowerCoefficients,
        powerPolynomialQ_twiceXPowerCoefficients, ih1, ih0]
      simp [Polynomial.Chebyshev.T_add_two]

/-- Convert a rational Chebyshev coefficient list, beginning at index `start`,
to a rational power-basis coefficient list. -/
def chebyshevCombinationPowerFrom : ℕ → List ℚ → List ℚ
  | _, [] => []
  | start, coefficient :: coefficients =>
      addPowerCoefficients
        (scalePowerCoefficients coefficient (chebyshevPowerCoefficients start))
        (chebyshevCombinationPowerFrom (start + 1) coefficients)

/-- Accumulate the combination while generating each successive Chebyshev polynomial once.
The pair carries the current and next power-coefficient lists. -/
private def chebyshevCombinationPowerAux : List ℚ → List ℚ → List ℚ → List ℚ
  | [], _, _ => []
  | coefficient :: coefficients, current, next =>
      addPowerCoefficients (scalePowerCoefficients coefficient current)
        (chebyshevCombinationPowerAux coefficients next
          (subPowerCoefficients (twiceXPowerCoefficients next) current))

private theorem chebyshevCombinationPowerAux_eq (coefficients : List ℚ) (start : ℕ) :
    chebyshevCombinationPowerAux coefficients (chebyshevPowerCoefficients start)
        (chebyshevPowerCoefficients (start + 1)) =
      chebyshevCombinationPowerFrom start coefficients := by
  induction coefficients generalizing start with
  | nil => rfl
  | cons coefficient coefficients ih =>
      change addPowerCoefficients _
        (chebyshevCombinationPowerAux coefficients (chebyshevPowerCoefficients (start + 1))
          (chebyshevPowerCoefficients (start + 2))) = _
      rw [ih]
      rfl

/-- Convert a rational Chebyshev coefficient list to power basis in a single recurrence.
The specification `chebyshevCombinationPowerFrom` is retained for algebraic proofs;
its separately recursive polynomial evaluation must not be used for native replay. -/
def chebyshevCombinationPower (coefficients : List ℚ) : List ℚ :=
  chebyshevCombinationPowerAux coefficients [1] [0, 1]

theorem chebyshevCombinationPower_eq_from (coefficients : List ℚ) :
    chebyshevCombinationPower coefficients = chebyshevCombinationPowerFrom 0 coefficients :=
  chebyshevCombinationPowerAux_eq coefficients 0

/-- The same rational coefficient list interpreted in the Chebyshev basis,
beginning at index `start`. -/
noncomputable def rationalChebyshevPolynomialQFrom : ℕ → List ℚ → ℚ[X]
  | _, [] => 0
  | start, coefficient :: coefficients =>
      C coefficient * Polynomial.Chebyshev.T ℚ (start : ℤ) +
        rationalChebyshevPolynomialQFrom (start + 1) coefficients

noncomputable def rationalChebyshevPolynomialQ (coefficients : List ℚ) : ℚ[X] :=
  rationalChebyshevPolynomialQFrom 0 coefficients

theorem powerPolynomialQ_chebyshevCombinationPowerFrom
    (start : ℕ) (coefficients : List ℚ) :
    powerPolynomialQ (chebyshevCombinationPowerFrom start coefficients) =
      rationalChebyshevPolynomialQFrom start coefficients := by
  induction coefficients generalizing start with
  | nil => simp [chebyshevCombinationPowerFrom, rationalChebyshevPolynomialQFrom,
      powerPolynomialQ]
  | cons coefficient coefficients ih =>
      rw [chebyshevCombinationPowerFrom, powerPolynomialQ_addPowerCoefficients,
        powerPolynomialQ_scalePowerCoefficients,
        powerPolynomialQ_chebyshevPowerCoefficients, ih]
      rfl

theorem powerPolynomialQ_chebyshevCombinationPower (coefficients : List ℚ) :
    powerPolynomialQ (chebyshevCombinationPower coefficients) =
      rationalChebyshevPolynomialQ coefficients := by
  rw [chebyshevCombinationPower_eq_from]
  exact powerPolynomialQ_chebyshevCombinationPowerFrom 0 coefficients

/-- A rational cosine polynomial, with the head coefficient starting at
frequency `start`. -/
noncomputable def rationalCosineValueFrom : ℕ → List ℚ → ℝ → ℝ
  | _, [], _ => 0
  | start, coefficient :: coefficients, x =>
      (coefficient : ℝ) * Real.cos ((start : ℝ) * x) +
        rationalCosineValueFrom (start + 1) coefficients x

noncomputable def rationalCosineValue (coefficients : List ℚ) (x : ℝ) : ℝ :=
  rationalCosineValueFrom 0 coefficients x

/-! ## Exact Fourier-shape and expectation contracts -/

/-- Arithmetic facts needed to bound a central-regime Fourier expectation.
The objective deliberately remains an independently frozen rational bound. -/
def CentralFourierContract (fourier : List ℚ) (degree : ℕ)
    (phiOne phiTwo objective : ℚ) : Prop :=
  2 ≤ degree ∧
    fourier.length = degree + 1 ∧
    0 ≤ fourier.getD 1 0 ∧
    0 ≤ fourier.getD 2 0 ∧
    (∀ j, 3 ≤ j → j < fourier.length → fourier.getD j 0 ≤ 0) ∧
    fourier.getD 0 0 + fourier.getD 1 0 * phiOne +
      fourier.getD 2 0 * phiTwo ≤ objective

/-- Arithmetic facts needed to bound a diffuse-regime Fourier expectation. -/
def DiffuseFourierContract (fourier : List ℚ) (degree : ℕ)
    (momentBound objective : ℚ) : Prop :=
  1 ≤ degree ∧
    fourier.length = degree + 1 ∧
    0 ≤ fourier.getD 1 0 ∧
    (∀ j, 2 ≤ j → j < fourier.length → fourier.getD j 0 ≤ 0) ∧
    fourier.getD 0 0 + fourier.getD 1 0 * momentBound ≤ objective

/-- Evaluate a Fourier coefficient list against an abstract moment sequence,
starting with moment index `start`. -/
noncomputable def rationalFourierExpectationFrom
    (start : ℕ) : List ℚ → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | coefficient :: coefficients, moment =>
      (coefficient : ℝ) * moment start +
        rationalFourierExpectationFrom (start + 1) coefficients moment

noncomputable def rationalFourierExpectation
    (coefficients : List ℚ) (moment : ℕ → ℝ) : ℝ :=
  rationalFourierExpectationFrom 0 coefficients moment

theorem integrable_rationalCosineValueFrom
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (start : ℕ) (coefficients : List ℚ) (phase : Ω → ℝ)
    (hintegrable : ∀ j : ℕ, Integrable
      (fun z => Real.cos ((j : ℝ) * phase z)) μ) :
    Integrable (fun z => rationalCosineValueFrom start coefficients (phase z)) μ := by
  induction coefficients generalizing start with
  | nil => simp [rationalCosineValueFrom]
  | cons coefficient coefficients ih =>
      simp only [rationalCosineValueFrom]
      exact ((hintegrable start).const_mul (coefficient : ℝ)).add
        (ih (start + 1))

/-- Integrating a rational cosine polynomial is exactly evaluation of the
same coefficient list against its sequence of cosine moments. -/
theorem integral_rationalCosineValueFrom
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (start : ℕ) (coefficients : List ℚ) (phase : Ω → ℝ)
    (hintegrable : ∀ j : ℕ, Integrable
      (fun z => Real.cos ((j : ℝ) * phase z)) μ) :
    (∫ z, rationalCosineValueFrom start coefficients (phase z) ∂μ) =
      rationalFourierExpectationFrom start coefficients
        (fun j => ∫ z, Real.cos ((j : ℝ) * phase z) ∂μ) := by
  induction coefficients generalizing start with
  | nil => simp [rationalCosineValueFrom, rationalFourierExpectationFrom]
  | cons coefficient coefficients ih =>
      simp only [rationalCosineValueFrom, rationalFourierExpectationFrom]
      rw [integral_add ((hintegrable start).const_mul (coefficient : ℝ))
        (integrable_rationalCosineValueFrom μ (start + 1) coefficients phase hintegrable),
        integral_const_mul, ih]

theorem integral_rationalCosineValue
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (coefficients : List ℚ) (phase : Ω → ℝ)
    (hintegrable : ∀ j : ℕ, Integrable
      (fun z => Real.cos ((j : ℝ) * phase z)) μ) :
    (∫ z, rationalCosineValue coefficients (phase z) ∂μ) =
      rationalFourierExpectation coefficients
        (fun j => ∫ z, Real.cos ((j : ℝ) * phase z) ∂μ) :=
  integral_rationalCosineValueFrom μ 0 coefficients phase hintegrable

theorem rationalFourierExpectationFrom_nonpos
    {start : ℕ} {coefficients : List ℚ} {moment : ℕ → ℝ}
    (hcoefficients : ∀ k < coefficients.length, coefficients.getD k 0 ≤ 0)
    (hmoment : ∀ j, 0 ≤ moment j) :
    rationalFourierExpectationFrom start coefficients moment ≤ 0 := by
  induction coefficients generalizing start with
  | nil => simp [rationalFourierExpectationFrom]
  | cons coefficient coefficients ih =>
      have hcoefficient : coefficient ≤ 0 := by
        simpa using hcoefficients 0 (by simp)
      have htail : ∀ k < coefficients.length, coefficients.getD k 0 ≤ 0 := by
        intro k hk
        simpa using hcoefficients (k + 1) (by simp [hk])
      have hhead : (coefficient : ℝ) * moment start ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hcoefficient) (hmoment start)
      have hrest := ih (start := start + 1) htail
      simp only [rationalFourierExpectationFrom]
      linarith

theorem rationalFourierExpectation_le_of_centralContract
    {fourier : List ℚ} {degree : ℕ} {phiOne phiTwo objective : ℚ}
    {moment : ℕ → ℝ}
    (hcontract : CentralFourierContract fourier degree phiOne phiTwo objective)
    (hmomentZero : moment 0 = 1)
    (hmomentNonnegative : ∀ j, 0 ≤ moment j)
    (hmomentOne : moment 1 ≤ (phiOne : ℝ))
    (hmomentTwo : moment 2 ≤ (phiTwo : ℝ)) :
    rationalFourierExpectation fourier moment ≤ (objective : ℝ) := by
  rcases hcontract with ⟨hdegree, hlength, hone, htwo, htail, hobjective⟩
  cases fourier with
  | nil => simp at hlength
  | cons c0 rest =>
      cases rest with
      | nil => simp at hlength; omega
      | cons c1 rest =>
          cases rest with
          | nil => simp at hlength; omega
          | cons c2 tail =>
              have htail' : ∀ k < tail.length, tail.getD k 0 ≤ 0 := by
                intro k hk
                simpa using htail (k + 3) (by omega) (by simp; omega)
              have hrest := rationalFourierExpectationFrom_nonpos
                (start := 3) htail' hmomentNonnegative
              have hfirst : (c1 : ℝ) * moment 1 ≤ (c1 : ℝ) * (phiOne : ℝ) :=
                mul_le_mul_of_nonneg_left hmomentOne (by exact_mod_cast hone)
              have hsecond : (c2 : ℝ) * moment 2 ≤ (c2 : ℝ) * (phiTwo : ℝ) :=
                mul_le_mul_of_nonneg_left hmomentTwo (by exact_mod_cast htwo)
              have hobjectiveQ : c0 + c1 * phiOne + c2 * phiTwo ≤ objective := by
                simpa using hobjective
              have hobjectiveR :
                  (c0 : ℝ) + (c1 : ℝ) * (phiOne : ℝ) +
                    (c2 : ℝ) * (phiTwo : ℝ) ≤ (objective : ℝ) := by
                exact_mod_cast hobjectiveQ
              unfold rationalFourierExpectation
              simp only [rationalFourierExpectationFrom]
              rw [hmomentZero]
              norm_num at hrest hfirst hsecond ⊢
              linarith

theorem rationalFourierExpectation_le_of_diffuseContract
    {fourier : List ℚ} {degree : ℕ} {momentBound objective : ℚ}
    {moment : ℕ → ℝ}
    (hcontract : DiffuseFourierContract fourier degree momentBound objective)
    (hmomentZero : moment 0 = 1)
    (hmomentNonnegative : ∀ j, 0 ≤ moment j)
    (hmomentOne : moment 1 ≤ (momentBound : ℝ)) :
    rationalFourierExpectation fourier moment ≤ (objective : ℝ) := by
  rcases hcontract with ⟨hdegree, hlength, hone, htail, hobjective⟩
  cases fourier with
  | nil => simp at hlength
  | cons c0 rest =>
      cases rest with
      | nil => simp at hlength; omega
      | cons c1 tail =>
          have htail' : ∀ k < tail.length, tail.getD k 0 ≤ 0 := by
            intro k hk
            simpa using htail (k + 2) (by omega) (by simp; omega)
          have hrest := rationalFourierExpectationFrom_nonpos
            (start := 2) htail' hmomentNonnegative
          have hfirst : (c1 : ℝ) * moment 1 ≤ (c1 : ℝ) * (momentBound : ℝ) :=
            mul_le_mul_of_nonneg_left hmomentOne (by exact_mod_cast hone)
          have hobjectiveQ : c0 + c1 * momentBound ≤ objective := by
            simpa using hobjective
          have hobjectiveR :
              (c0 : ℝ) + (c1 : ℝ) * (momentBound : ℝ) ≤ (objective : ℝ) := by
            exact_mod_cast hobjectiveQ
          unfold rationalFourierExpectation
          simp only [rationalFourierExpectationFrom]
          rw [hmomentZero]
          norm_num at hrest hfirst ⊢
          linarith

theorem integral_rationalCosineValue_le_of_centralContract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {fourier : List ℚ} {degree : ℕ} {phiOne phiTwo objective : ℚ}
    (phase : Ω → ℝ)
    (hcontract : CentralFourierContract fourier degree phiOne phiTwo objective)
    (hintegrable : ∀ j : ℕ, Integrable
      (fun z => Real.cos ((j : ℝ) * phase z)) μ)
    (hmomentZero : (∫ z, Real.cos ((0 : ℝ) * phase z) ∂μ) = 1)
    (hmomentNonnegative : ∀ j : ℕ,
      0 ≤ ∫ z, Real.cos ((j : ℝ) * phase z) ∂μ)
    (hmomentOne : (∫ z, Real.cos ((1 : ℝ) * phase z) ∂μ) ≤ (phiOne : ℝ))
    (hmomentTwo : (∫ z, Real.cos ((2 : ℝ) * phase z) ∂μ) ≤ (phiTwo : ℝ)) :
    (∫ z, rationalCosineValue fourier (phase z) ∂μ) ≤ (objective : ℝ) := by
  rw [integral_rationalCosineValue μ fourier phase hintegrable]
  exact rationalFourierExpectation_le_of_centralContract hcontract
    (by simpa using hmomentZero) hmomentNonnegative
    (by simpa using hmomentOne) (by simpa using hmomentTwo)

theorem integral_rationalCosineValue_le_of_diffuseContract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {fourier : List ℚ} {degree : ℕ} {momentBound objective : ℚ}
    (phase : Ω → ℝ)
    (hcontract : DiffuseFourierContract fourier degree momentBound objective)
    (hintegrable : ∀ j : ℕ, Integrable
      (fun z => Real.cos ((j : ℝ) * phase z)) μ)
    (hmomentZero : (∫ z, Real.cos ((0 : ℝ) * phase z) ∂μ) = 1)
    (hmomentNonnegative : ∀ j : ℕ,
      0 ≤ ∫ z, Real.cos ((j : ℝ) * phase z) ∂μ)
    (hmomentOne : (∫ z, Real.cos ((1 : ℝ) * phase z) ∂μ) ≤ (momentBound : ℝ)) :
    (∫ z, rationalCosineValue fourier (phase z) ∂μ) ≤ (objective : ℝ) := by
  rw [integral_rationalCosineValue μ fourier phase hintegrable]
  exact rationalFourierExpectation_le_of_diffuseContract hcontract
    (by simpa using hmomentZero) hmomentNonnegative (by simpa using hmomentOne)

theorem chebyshevQ_eval2_cos (n : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℚ (n : ℤ)).eval₂
        (Rat.castHom ℝ) (Real.cos x) =
      Real.cos ((n : ℝ) * x) := by
  rw [eval₂_eq_eval_map, Polynomial.Chebyshev.map_T,
    Polynomial.Chebyshev.T_real_cos]
  norm_num

theorem rationalChebyshevPolynomialQFrom_eval2_cos
    (start : ℕ) (coefficients : List ℚ) (x : ℝ) :
    (rationalChebyshevPolynomialQFrom start coefficients).eval₂
        (Rat.castHom ℝ) (Real.cos x) =
      rationalCosineValueFrom start coefficients x := by
  induction coefficients generalizing start with
  | nil => simp [rationalChebyshevPolynomialQFrom, rationalCosineValueFrom]
  | cons coefficient coefficients ih =>
      simp only [rationalChebyshevPolynomialQFrom, rationalCosineValueFrom,
        eval₂_add, eval₂_mul, eval₂_C, Rat.coe_castHom]
      rw [chebyshevQ_eval2_cos, ih]

theorem rationalChebyshevPolynomialQ_eval2_cos (coefficients : List ℚ) (x : ℝ) :
    (rationalChebyshevPolynomialQ coefficients).eval₂
        (Rat.castHom ℝ) (Real.cos x) =
      rationalCosineValue coefficients x :=
  rationalChebyshevPolynomialQFrom_eval2_cos 0 coefficients x

/-- A rational Bernstein-basis polynomial. -/
noncomputable def bernsteinPolynomialQ (n : ℕ) (coefficients : List ℚ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    C (coefficients.getD j 0) * bernsteinPolynomial ℚ n j

/-- Pull a polynomial on `[a,b]` back to the unit interval. -/
noncomputable def affinePullbackQ (p : ℚ[X]) (a b : ℚ) : ℚ[X] :=
  p.comp (C a + C (b - a) * X)

/-- Executable equality check for a small contiguous coefficient block. -/
def coefficientBlockCheck (p q : ℚ[X]) (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      decide (p.coeff start = q.coeff start) &&
        coefficientBlockCheck p q (start + 1) count

theorem coefficientBlockCheck_sound {p q : ℚ[X]} {start count : ℕ}
    (hcheck : coefficientBlockCheck p q start count = true) :
    ∀ k, start ≤ k → k < start + count → p.coeff k = q.coeff k := by
  induction count generalizing start with
  | zero =>
      intro k hstart hstop
      omega
  | succ count ih =>
      intro k hstart hstop
      rw [coefficientBlockCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨hhead, htail⟩
      by_cases hk : k = start
      · subst k
        exact of_decide_eq_true hhead
      · apply ih htail k (by omega) (by omega)

/-- Coefficient `j` after substituting `a + (b-a)X` into a power-basis
polynomial.  This direct formula keeps concrete checks executable without
reducing Mathlib's noncomputable polynomial representation. -/
def affinePowerCoefficient (coefficients : List ℚ) (a b : ℚ) (j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range coefficients.length,
    if j ≤ k then
      coefficients.getD k 0 * (k.choose j : ℚ) * a ^ (k - j) * (b - a) ^ j
    else 0

/-- Power-basis coefficient `j` of a degree-`n` Bernstein expansion. -/
def bernsteinPowerCoefficient (n : ℕ) (coefficients : List ℚ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1),
    if i ≤ j then
      coefficients.getD i 0 * (n.choose i : ℚ) * ((n - i).choose (j - i) : ℚ) *
        (-1 : ℚ) ^ (j - i)
    else 0

/-- Exact executable check that an affine power expansion and a Bernstein
expansion agree on a small contiguous coefficient block. -/
def bernsteinIdentityBlockCheck (power : List ℚ) (a b : ℚ) (n : ℕ)
    (bernstein : List ℚ) (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      decide (affinePowerCoefficient power a b start =
        bernsteinPowerCoefficient n bernstein start) &&
      bernsteinIdentityBlockCheck power a b n bernstein (start + 1) count

theorem bernsteinIdentityBlockCheck_sound {power : List ℚ} {a b : ℚ} {n : ℕ}
    {bernstein : List ℚ} {start count : ℕ}
    (hcheck : bernsteinIdentityBlockCheck power a b n bernstein start count = true) :
    ∀ k, start ≤ k → k < start + count →
      affinePowerCoefficient power a b k =
        bernsteinPowerCoefficient n bernstein k := by
  induction count generalizing start with
  | zero =>
      intro k hstart hstop
      omega
  | succ count ih =>
      intro k hstart hstop
      rw [bernsteinIdentityBlockCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨hhead, htail⟩
      by_cases hk : k = start
      · subst k
        exact of_decide_eq_true hhead
      · apply ih htail k (by omega) (by omega)

/-! ## Integer-scaled Bernstein identity checks -/

/-- Check that a rational coefficient block is represented by integer
numerators over one common denominator.  This is only linear in the block
length and avoids repeated rational normalization in the polynomial identity
check below. -/
def integerScaleBlockCheck (rational : List ℚ) (numerators : List ℤ)
    (denominator : ℤ) (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      decide (rational.getD start 0 * denominator = numerators.getD start 0) &&
        integerScaleBlockCheck rational numerators denominator (start + 1) count

theorem integerScaleBlockCheck_sound {rational : List ℚ} {numerators : List ℤ}
    {denominator : ℤ} {start count : ℕ}
    (hcheck : integerScaleBlockCheck rational numerators denominator start count = true) :
    ∀ k, start ≤ k → k < start + count →
      rational.getD k 0 * denominator = numerators.getD k 0 := by
  induction count generalizing start with
  | zero =>
      intro k hstart hstop
      omega
  | succ count ih =>
      intro k hstart hstop
      rw [integerScaleBlockCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨hhead, htail⟩
      by_cases hk : k = start
      · subst k
        exact of_decide_eq_true hhead
      · apply ih htail k (by omega) (by omega)

/-- The numerator of an affine power coefficient after scaling the power
coefficients by `powerDenominator` and both interval endpoints by
`intervalDenominator`.  The advertised degree supplies one common interval
denominator for every summand. -/
def integerAffinePowerCoefficient (numerators : List ℤ) (aNumerator deltaNumerator : ℤ)
    (intervalDenominator : ℤ) (n j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range numerators.length,
    if j ≤ k then
      numerators.getD k 0 * (k.choose j : ℤ) * aNumerator ^ (k - j) *
        deltaNumerator ^ j * intervalDenominator ^ (n - k)
    else 0

/-- The integer numerator of a Bernstein power coefficient whose Bernstein
coefficients share one denominator. -/
def integerBernsteinPowerCoefficient (n : ℕ) (numerators : List ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1),
    if i ≤ j then
      numerators.getD i 0 * (n.choose i : ℤ) * ((n - i).choose (j - i) : ℤ) *
        (-1 : ℤ) ^ (j - i)
    else 0

/-- Exact integer-only equality check for an affine/Bernstein coefficient
block.  All divisions have been factored into three common denominators, so
concrete replay uses only integer arithmetic. -/
def integerBernsteinIdentityBlockCheck (powerNumerators : List ℤ)
    (powerDenominator : ℤ) (aNumerator deltaNumerator intervalDenominator : ℤ)
    (n : ℕ) (bernsteinNumerators : List ℤ) (bernsteinDenominator : ℤ)
    (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      decide (bernsteinDenominator *
          integerAffinePowerCoefficient powerNumerators aNumerator deltaNumerator
            intervalDenominator n start =
        powerDenominator * intervalDenominator ^ n *
          integerBernsteinPowerCoefficient n bernsteinNumerators start) &&
        integerBernsteinIdentityBlockCheck powerNumerators powerDenominator
          aNumerator deltaNumerator intervalDenominator n bernsteinNumerators
          bernsteinDenominator (start + 1) count

theorem integerBernsteinIdentityBlockCheck_sound
    {powerNumerators : List ℤ} {powerDenominator : ℤ}
    {aNumerator deltaNumerator intervalDenominator : ℤ} {n : ℕ}
    {bernsteinNumerators : List ℤ} {bernsteinDenominator : ℤ}
    {start count : ℕ}
    (hcheck : integerBernsteinIdentityBlockCheck powerNumerators powerDenominator
      aNumerator deltaNumerator intervalDenominator n bernsteinNumerators
      bernsteinDenominator start count = true) :
    ∀ k, start ≤ k → k < start + count →
      bernsteinDenominator *
          integerAffinePowerCoefficient powerNumerators aNumerator deltaNumerator
            intervalDenominator n k =
        powerDenominator * intervalDenominator ^ n *
          integerBernsteinPowerCoefficient n bernsteinNumerators k := by
  induction count generalizing start with
  | zero =>
      intro k hstart hstop
      omega
  | succ count ih =>
      intro k hstart hstop
      rw [integerBernsteinIdentityBlockCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨hhead, htail⟩
      by_cases hk : k = start
      · subst k
        exact of_decide_eq_true hhead
      · apply ih htail k (by omega) (by omega)

private theorem integerAffinePowerCoefficient_sound
    {rational : List ℚ} {numerators : List ℤ} {powerDenominator : ℤ}
    {a b : ℚ} {aNumerator deltaNumerator intervalDenominator : ℤ} {n j : ℕ}
    (hrationalLength : rational.length = n + 1)
    (hnumeratorsLength : numerators.length = n + 1)
    (hscale : ∀ k ≤ n,
      rational.getD k 0 * powerDenominator = numerators.getD k 0)
    (ha : a * intervalDenominator = aNumerator)
    (hdelta : (b - a) * intervalDenominator = deltaNumerator)
    (_hj : j ≤ n) :
    affinePowerCoefficient rational a b j *
        (powerDenominator * intervalDenominator ^ n) =
      (integerAffinePowerCoefficient numerators aNumerator deltaNumerator
        intervalDenominator n j : ℚ) := by
  unfold affinePowerCoefficient integerAffinePowerCoefficient
  rw [Finset.sum_mul]
  push_cast
  apply Finset.sum_congr
  · simp [hrationalLength, hnumeratorsLength]
  intro k hk
  simp only [Finset.mem_range] at hk
  by_cases hjk : j ≤ k
  · rw [if_pos hjk, if_pos hjk]
    rw [← hscale k (by omega), ← ha, ← hdelta]
    rw [mul_pow, mul_pow]
    have hn : n = (k - j) + j + (n - k) := by omega
    conv_lhs =>
      rhs
      rw [hn, pow_add, pow_add]
    ring
  · rw [if_neg hjk, if_neg hjk]
    simp

private theorem integerBernsteinPowerCoefficient_sound
    {rational : List ℚ} {numerators : List ℤ} {bernsteinDenominator : ℤ}
    {n j : ℕ}
    (hscale : ∀ i ≤ n,
      rational.getD i 0 * bernsteinDenominator = numerators.getD i 0) :
    bernsteinPowerCoefficient n rational j * bernsteinDenominator =
      (integerBernsteinPowerCoefficient n numerators j : ℚ) := by
  unfold bernsteinPowerCoefficient integerBernsteinPowerCoefficient
  rw [Finset.sum_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  by_cases hij : i ≤ j
  · rw [if_pos hij, if_pos hij]
    rw [← hscale i (by omega)]
    ring
  · rw [if_neg hij, if_neg hij]
    simp

/-- Soundness of the integer-scaled checker against the original rational
coefficient formulas.  The scale hypotheses are themselves discharged by the
linear `integerScaleBlockCheck`; the only quadratic work left in a generated
leaf is integer arithmetic. -/
theorem integerBernsteinIdentityCoefficient_sound
    {power : List ℚ} {powerNumerators : List ℤ} {powerDenominator : ℤ}
    {a b : ℚ} {aNumerator deltaNumerator intervalDenominator : ℤ} {n k : ℕ}
    {bernstein : List ℚ} {bernsteinNumerators : List ℤ}
    {bernsteinDenominator : ℤ}
    (hpowerLength : power.length = n + 1)
    (hpowerNumeratorsLength : powerNumerators.length = n + 1)
    (hpowerScale : ∀ i ≤ n,
      power.getD i 0 * powerDenominator = powerNumerators.getD i 0)
    (hbernsteinScale : ∀ i ≤ n,
      bernstein.getD i 0 * bernsteinDenominator = bernsteinNumerators.getD i 0)
    (ha : a * intervalDenominator = aNumerator)
    (hdelta : (b - a) * intervalDenominator = deltaNumerator)
    (hpowerDenominator : powerDenominator ≠ 0)
    (hintervalDenominator : intervalDenominator ≠ 0)
    (hbernsteinDenominator : bernsteinDenominator ≠ 0)
    (hk : k ≤ n)
    (hidentity : bernsteinDenominator *
          integerAffinePowerCoefficient powerNumerators aNumerator deltaNumerator
            intervalDenominator n k =
        powerDenominator * intervalDenominator ^ n *
          integerBernsteinPowerCoefficient n bernsteinNumerators k) :
    affinePowerCoefficient power a b k =
      bernsteinPowerCoefficient n bernstein k := by
  have haffine := integerAffinePowerCoefficient_sound
    hpowerLength hpowerNumeratorsLength hpowerScale ha hdelta hk
  have hbernstein := integerBernsteinPowerCoefficient_sound
    (j := k) hbernsteinScale
  have hidentityQ : (bernsteinDenominator : ℚ) *
          (integerAffinePowerCoefficient powerNumerators aNumerator deltaNumerator
            intervalDenominator n k : ℚ) =
        ((powerDenominator : ℚ) * (intervalDenominator : ℚ) ^ n) *
          (integerBernsteinPowerCoefficient n bernsteinNumerators k : ℚ) := by
    exact_mod_cast hidentity
  have hscale : ((powerDenominator : ℚ) * (intervalDenominator : ℚ) ^ n) *
      (bernsteinDenominator : ℚ) ≠ 0 := by
    positivity
  apply mul_right_cancel₀ hscale
  calc
    affinePowerCoefficient power a b k *
          (((powerDenominator : ℚ) * (intervalDenominator : ℚ) ^ n) *
            (bernsteinDenominator : ℚ)) =
        (bernsteinDenominator : ℚ) *
          (affinePowerCoefficient power a b k *
            ((powerDenominator : ℚ) * (intervalDenominator : ℚ) ^ n)) := by ring
    _ = (bernsteinDenominator : ℚ) *
          (integerAffinePowerCoefficient powerNumerators aNumerator deltaNumerator
            intervalDenominator n k : ℚ) := by rw [haffine]
    _ = ((powerDenominator : ℚ) * (intervalDenominator : ℚ) ^ n) *
          (integerBernsteinPowerCoefficient n bernsteinNumerators k : ℚ) := hidentityQ
    _ = ((powerDenominator : ℚ) * (intervalDenominator : ℚ) ^ n) *
          (bernsteinPowerCoefficient n bernstein k * bernsteinDenominator) := by
        rw [hbernstein]
    _ = bernsteinPowerCoefficient n bernstein k *
          (((powerDenominator : ℚ) * (intervalDenominator : ℚ) ^ n) *
            (bernsteinDenominator : ℚ)) := by ring

/-- Exact nonnegativity check for a contiguous block of rational
coefficients. -/
def nonnegativeBlockCheck (coefficients : List ℚ) (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      decide (0 ≤ coefficients.getD start 0) &&
        nonnegativeBlockCheck coefficients (start + 1) count

theorem nonnegativeBlockCheck_sound {coefficients : List ℚ} {start count : ℕ}
    (hcheck : nonnegativeBlockCheck coefficients start count = true) :
    ∀ k, start ≤ k → k < start + count → 0 ≤ coefficients.getD k 0 := by
  induction count generalizing start with
  | zero =>
      intro k hstart hstop
      omega
  | succ count ih =>
      intro k hstart hstop
      rw [nonnegativeBlockCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨hhead, htail⟩
      by_cases hk : k = start
      · subst k
        exact of_decide_eq_true hhead
      · apply ih htail k (by omega) (by omega)

/-- Exact nonpositivity check for a contiguous block of rational
coefficients. -/
def nonpositiveBlockCheck (coefficients : List ℚ) (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      decide (coefficients.getD start 0 ≤ 0) &&
        nonpositiveBlockCheck coefficients (start + 1) count

theorem nonpositiveBlockCheck_sound {coefficients : List ℚ} {start count : ℕ}
    (hcheck : nonpositiveBlockCheck coefficients start count = true) :
    ∀ k, start ≤ k → k < start + count → coefficients.getD k 0 ≤ 0 := by
  induction count generalizing start with
  | zero =>
      intro k hstart hstop
      omega
  | succ count ih =>
      intro k hstart hstop
      rw [nonpositiveBlockCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨hhead, htail⟩
      by_cases hk : k = start
      · subst k
        exact of_decide_eq_true hhead
      · apply ih htail k (by omega) (by omega)

private theorem one_sub_X_pow_coeff (m k : ℕ) :
    (((1 - X) ^ m : ℚ[X]).coeff k) = (m.choose k : ℚ) * (-1 : ℚ) ^ k := by
  rw [show (1 - X : ℚ[X]) = (1 + X).comp (C (-1) * X) by
    simp only [Polynomial.add_comp, one_comp, X_comp]
    rw [sub_eq_add_neg]
    simp only [C_neg, map_one, neg_mul, one_mul]]
  rw [← pow_comp, comp_C_mul_X_coeff, coeff_one_add_X_pow]

private theorem bernsteinPolynomial_coeff (n i k : ℕ) :
    (bernsteinPolynomial ℚ n i).coeff k = if i ≤ k then
      (n.choose i : ℚ) * ((n - i).choose (k - i) : ℚ) *
        (-1 : ℚ) ^ (k - i) else 0 := by
  rw [bernsteinPolynomial]
  by_cases h : i ≤ k
  · rw [if_pos h]
    simp only [mul_assoc, coeff_natCast_mul]
    rw [show k = (k - i) + i by omega, coeff_X_pow_mul, one_sub_X_pow_coeff,
      Nat.sub_add_cancel h]
  · rw [if_neg h]
    simp only [mul_assoc, coeff_natCast_mul]
    simp only [coeff_mul, coeff_X_pow]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro pair hpair
    by_cases hp : pair.1 = i
    · have hsum := Finset.mem_antidiagonal.mp hpair
      exfalso
      omega
    · simp [hp]

private theorem affine_pow_coeff (a d : ℚ) (k j : ℕ) :
    ((C a + C d * X) ^ k).coeff j = if j ≤ k then
      (k.choose j : ℚ) * a ^ (k - j) * d ^ j else 0 := by
  rw [show (C a + C d * X) ^ k = ((X + C a) ^ k).comp (C d * X) by
    rw [pow_comp]
    simp only [Polynomial.add_comp, X_comp, C_comp]
    ring]
  rw [comp_C_mul_X_coeff, coeff_X_add_C_pow]
  by_cases h : j ≤ k
  · rw [if_pos h]
    ring
  · rw [if_neg h, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]
    simp

theorem affinePullbackQ_coeff (coefficients : List ℚ) (a b : ℚ) (j : ℕ) :
    (affinePullbackQ (powerPolynomialQ coefficients) a b).coeff j =
      affinePowerCoefficient coefficients a b j := by
  unfold affinePullbackQ powerPolynomialQ affinePowerCoefficient
  change ((Polynomial.compRingHom (C a + C (b - a) * X))
    (∑ k ∈ Finset.range coefficients.length,
      C (coefficients.getD k 0) * X ^ k)).coeff j = _
  rw [map_sum]
  let coeffHom : ℚ[X] →+ ℚ :=
    { toFun := fun p => p.coeff j
      map_zero' := coeff_zero j
      map_add' := fun p q => coeff_add p q j }
  change coeffHom (∑ k ∈ Finset.range coefficients.length,
    (C a + C (b - a) * X).compRingHom
      (C (coefficients.getD k 0) * X ^ k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change ((C (coefficients.getD k 0) * X ^ k).comp
    (C a + C (b - a) * X)).coeff j = _
  rw [mul_comp, C_comp, pow_comp, X_comp, coeff_C_mul, affine_pow_coeff]
  split <;> ring

theorem bernsteinPolynomialQ_coeff (n : ℕ) (coefficients : List ℚ) (j : ℕ) :
    (bernsteinPolynomialQ n coefficients).coeff j =
      bernsteinPowerCoefficient n coefficients j := by
  unfold bernsteinPolynomialQ bernsteinPowerCoefficient
  let coeffHom : ℚ[X] →+ ℚ :=
    { toFun := fun p => p.coeff j
      map_zero' := coeff_zero j
      map_add' := fun p q => coeff_add p q j }
  change coeffHom (∑ i ∈ Finset.range (n + 1),
    C (coefficients.getD i 0) * bernsteinPolynomial ℚ n i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (C (coefficients.getD i 0) * bernsteinPolynomial ℚ n i).coeff j = _
  rw [coeff_C_mul, bernsteinPolynomial_coeff]
  split <;> ring

/-- Coefficientwise agreement through the advertised degree proves the exact
rational affine/Bernstein identity.  Length hypotheses prevent `getD` from
silently padding malformed certificate vectors. -/
theorem affinePullbackQ_eq_bernsteinPolynomialQ {power bernstein : List ℚ}
    {a b : ℚ} {n : ℕ} (hpowerLength : power.length = n + 1)
    (hbernsteinLength : bernstein.length = n + 1)
    (hcoeff : ∀ k ≤ n, affinePowerCoefficient power a b k =
      bernsteinPowerCoefficient n bernstein k) :
    affinePullbackQ (powerPolynomialQ power) a b =
      bernsteinPolynomialQ n bernstein := by
  ext k
  rw [affinePullbackQ_coeff, bernsteinPolynomialQ_coeff]
  by_cases hk : k ≤ n
  · exact hcoeff k hk
  · have hnk : n < k := Nat.lt_of_not_ge hk
    have hleft : affinePowerCoefficient power a b k = 0 := by
      unfold affinePowerCoefficient
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range, hpowerLength] at hi
      rw [if_neg (by omega)]
    have hright : bernsteinPowerCoefficient n bernstein k = 0 := by
      unfold bernsteinPowerCoefficient
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega)]
      rw [Nat.choose_eq_zero_of_lt
        (Nat.sub_lt_sub_right (by omega) hnk)]
      ring
    rw [hleft, hright]

/-- A common-denominator integer certificate proves the same exact rational
polynomial identity as the legacy rational convolution checker. -/
theorem affinePullbackQ_eq_bernsteinPolynomialQ_of_integerCertificate
    {power : List ℚ} {powerNumerators : List ℤ} {powerDenominator : ℤ}
    {a b : ℚ} {aNumerator deltaNumerator intervalDenominator : ℤ} {n : ℕ}
    {bernstein : List ℚ} {bernsteinNumerators : List ℤ}
    {bernsteinDenominator : ℤ}
    (hpowerLength : power.length = n + 1)
    (hbernsteinLength : bernstein.length = n + 1)
    (hpowerNumeratorsLength : powerNumerators.length = n + 1)
    (hpowerScale : ∀ i ≤ n,
      power.getD i 0 * powerDenominator = powerNumerators.getD i 0)
    (hbernsteinScale : ∀ i ≤ n,
      bernstein.getD i 0 * bernsteinDenominator = bernsteinNumerators.getD i 0)
    (ha : a * intervalDenominator = aNumerator)
    (hdelta : (b - a) * intervalDenominator = deltaNumerator)
    (hpowerDenominator : powerDenominator ≠ 0)
    (hintervalDenominator : intervalDenominator ≠ 0)
    (hbernsteinDenominator : bernsteinDenominator ≠ 0)
    (hcheck : integerBernsteinIdentityBlockCheck powerNumerators powerDenominator
      aNumerator deltaNumerator intervalDenominator n bernsteinNumerators
      bernsteinDenominator 0 (n + 1) = true) :
    affinePullbackQ (powerPolynomialQ power) a b =
      bernsteinPolynomialQ n bernstein := by
  apply affinePullbackQ_eq_bernsteinPolynomialQ hpowerLength hbernsteinLength
  intro k hk
  apply integerBernsteinIdentityCoefficient_sound hpowerLength
    hpowerNumeratorsLength hpowerScale hbernsteinScale ha hdelta
    hpowerDenominator hintervalDenominator hbernsteinDenominator hk
  exact integerBernsteinIdentityBlockCheck_sound hcheck k (by omega) (by omega)

/-- A rational power polynomial evaluated in the reals. -/
noncomputable def rationalPowerValue (coefficients : List ℚ) (x : ℝ) : ℝ :=
  (powerPolynomialQ coefficients).eval₂ (Rat.castHom ℝ) x

/-- A checked Chebyshev-to-power conversion identifies the certified power
polynomial with the cosine polynomial named by the source Fourier data. -/
theorem rationalPowerValue_cos_eq_rationalCosineValue
    {fourier power : List ℚ}
    (hbridge : chebyshevCombinationPower fourier = power) (x : ℝ) :
    rationalPowerValue power (Real.cos x) =
      rationalCosineValue fourier x := by
  unfold rationalPowerValue
  rw [← hbridge, powerPolynomialQ_chebyshevCombinationPower,
    rationalChebyshevPolynomialQ_eval2_cos]

theorem rationalPowerValue_subtractConstant (c : ℚ) (coefficients : List ℚ)
    (r : ℚ) (x : ℝ) :
    rationalPowerValue (subtractConstant (c :: coefficients) r) x =
      rationalPowerValue (c :: coefficients) x - (r : ℝ) := by
  unfold rationalPowerValue
  rw [powerPolynomialQ_subtractConstant, eval₂_sub, eval₂_C]
  simp only [Rat.coe_castHom]

theorem rationalPowerValue_subtractConstant_of_ne_nil {coefficients : List ℚ}
    (hcoefficients : coefficients ≠ []) (r : ℚ) (x : ℝ) :
    rationalPowerValue (subtractConstant coefficients r) x =
      rationalPowerValue coefficients x - (r : ℝ) := by
  cases coefficients with
  | nil => contradiction
  | cons c coefficients =>
      exact rationalPowerValue_subtractConstant c coefficients r x

/-- A rational Bernstein expansion evaluated in the reals. -/
noncomputable def rationalBernsteinValue (n : ℕ) (coefficients : List ℚ)
    (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (coefficients.getD j 0 : ℝ) * (n.choose j : ℝ) *
      t ^ j * (1 - t) ^ (n - j)

theorem rationalBernsteinValue_nonneg {n : ℕ} {coefficients : List ℚ} {t : ℝ}
    (hcoefficients : ∀ j < n + 1, 0 ≤ coefficients.getD j 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ rationalBernsteinValue n coefficients t := by
  unfold rationalBernsteinValue
  apply Finset.sum_nonneg
  intro j hj
  rw [Finset.mem_range] at hj
  have hcoefficient : (0 : ℝ) ≤ (coefficients.getD j 0 : ℚ) := by
    exact_mod_cast hcoefficients j hj
  have hone : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hcoefficient (by positivity))
      (pow_nonneg ht0 j))
    (pow_nonneg hone (n - j))

private theorem bernsteinPolynomialQ_eval2 (n : ℕ) (coefficients : List ℚ)
    (t : ℝ) :
    (bernsteinPolynomialQ n coefficients).eval₂ (Rat.castHom ℝ) t =
      rationalBernsteinValue n coefficients t := by
  simp only [bernsteinPolynomialQ, rationalBernsteinValue, eval₂_finsetSum,
    eval₂_mul, eval₂_C, bernsteinPolynomial]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval₂_natCast, eval₂_pow, eval₂_X, eval₂_sub, eval₂_one]
  simp only [Rat.coe_castHom]
  ring

theorem rationalPowerValue_affine_eq_bernstein {power bernstein : List ℚ}
    {a b : ℚ} {n : ℕ}
    (hidentity : affinePullbackQ (powerPolynomialQ power) a b =
      bernsteinPolynomialQ n bernstein) (t : ℝ) :
    rationalPowerValue power ((a : ℝ) + ((b : ℝ) - (a : ℝ)) * t) =
      rationalBernsteinValue n bernstein t := by
  have heval := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℝ) t) hidentity
  rw [affinePullbackQ, eval₂_comp, bernsteinPolynomialQ_eval2] at heval
  convert heval using 1
  · unfold rationalPowerValue
    congr 1
    simp

theorem rationalPowerValue_nonneg_on_interval {power bernstein : List ℚ}
    {a b : ℚ} {n : ℕ} {y : ℝ} (hab : a < b)
    (hya : (a : ℝ) ≤ y) (hyb : y ≤ (b : ℝ))
    (hidentity : affinePullbackQ (powerPolynomialQ power) a b =
      bernsteinPolynomialQ n bernstein)
    (hcoefficients : ∀ j < n + 1, 0 ≤ bernstein.getD j 0) :
    0 ≤ rationalPowerValue power y := by
  let t : ℝ := (y - (a : ℝ)) / ((b : ℝ) - (a : ℝ))
  have hba : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by exact_mod_cast sub_pos.mpr hab
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hba).2 (by linarith)
  have hy : y = (a : ℝ) + ((b : ℝ) - (a : ℝ)) * t := by
    dsimp [t]
    field_simp [hba.ne']
    ring
  rw [hy, rationalPowerValue_affine_eq_bernstein hidentity]
  exact rationalBernsteinValue_nonneg hcoefficients ht0 ht1

/-- A structurally complete dyadic interval certificate.  A branch always
contains proofs for both halves, so omitting an adaptive leaf cannot produce
a proof for the parent interval. -/
inductive NonnegativeTree (F : ℝ → ℝ) : ℚ → ℚ → Prop
  | leaf {a b : ℚ} (bound : ∀ y : ℝ, (a : ℝ) ≤ y → y ≤ (b : ℝ) → 0 ≤ F y) :
      NonnegativeTree F a b
  | branch {a b : ℚ}
      (left : NonnegativeTree F a ((a + b) / 2))
      (right : NonnegativeTree F ((a + b) / 2) b) :
      NonnegativeTree F a b

theorem NonnegativeTree.nonneg {F : ℝ → ℝ} {a b : ℚ}
    (certificate : NonnegativeTree F a b) {y : ℝ}
    (hya : (a : ℝ) ≤ y) (hyb : y ≤ (b : ℝ)) : 0 ≤ F y := by
  induction certificate with
  | leaf bound => exact bound y hya hyb
  | @branch a b left right ihLeft ihRight =>
      by_cases hmid : y ≤ (((a + b) / 2 : ℚ) : ℝ)
      · exact ihLeft hya hmid
      · exact ihRight (le_of_not_ge hmid) hyb

theorem polynomial_eq_of_degree_le_of_blocks {p q : ℚ[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hcoeff : ∀ k ≤ n, p.coeff k = q.coeff k) : p = q := by
  ext k
  by_cases hk : k ≤ n
  · exact hcoeff k hk
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hnk),
      coeff_eq_zero_of_natDegree_lt (hq.trans_lt hnk)]

theorem bernsteinPolynomialQ_eval (n : ℕ) (coefficients : List ℚ) (t : ℚ) :
    (bernsteinPolynomialQ n coefficients).eval t =
      ∑ j ∈ Finset.range (n + 1),
        coefficients.getD j 0 * (n.choose j : ℚ) * t ^ j * (1 - t) ^ (n - j) := by
  simp only [bernsteinPolynomialQ, bernsteinPolynomial, eval_finsetSum, eval_mul,
    eval_C, eval_natCast, eval_X, eval_pow, eval_sub, eval_one]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A finite power-basis polynomial evaluated at a real argument. -/
noncomputable def powerValue (coefficients : List ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range coefficients.length, coefficients.getD j 0 * x ^ j

/-- A finite cosine polynomial with coefficient `j` multiplying `cos (j * x)`. -/
noncomputable def cosinePolynomial (coefficients : List ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range coefficients.length,
    coefficients.getD j 0 * Real.cos ((j : ℝ) * x)

/-- The same coefficient list interpreted in the Chebyshev basis. -/
noncomputable def chebyshevPolynomial (coefficients : List ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range coefficients.length,
    C (coefficients.getD j 0) * Polynomial.Chebyshev.T ℝ j

theorem eval_chebyshevPolynomial_cos (coefficients : List ℝ) (x : ℝ) :
    (chebyshevPolynomial coefficients).eval (Real.cos x) =
      cosinePolynomial coefficients x := by
  simp only [chebyshevPolynomial, cosinePolynomial, eval_finsetSum, eval_mul, eval_C,
    Polynomial.Chebyshev.T_real_cos]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2

/-- The value of a degree-`n` Bernstein expansion on the unit interval. -/
noncomputable def bernsteinValue (n : ℕ) (coefficients : List ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    coefficients.getD j 0 * (n.choose j : ℝ) * t ^ j * (1 - t) ^ (n - j)

theorem bernsteinValue_nonneg {n : ℕ} {coefficients : List ℝ} {t : ℝ}
    (hcoefficients : ∀ j < n + 1, 0 ≤ coefficients.getD j 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bernsteinValue n coefficients t := by
  unfold bernsteinValue
  apply Finset.sum_nonneg
  intro j hj
  rw [Finset.mem_range] at hj
  have hone : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (hcoefficients j hj) (by positivity))
      (pow_nonneg ht0 j))
    (pow_nonneg hone (n - j))

/-- A Bernstein expansion with nonnegative coefficients proves nonnegativity
on any affine image of the unit interval. -/
theorem nonneg_on_interval_of_bernstein {n : ℕ} {coefficients : List ℝ}
    {F : ℝ → ℝ} {a b y : ℝ}
    (hab : a < b) (hya : a ≤ y) (hyb : y ≤ b)
    (hidentity : ∀ t, F (a + (b - a) * t) = bernsteinValue n coefficients t)
    (hcoefficients : ∀ j < n + 1, 0 ≤ coefficients.getD j 0) :
    0 ≤ F y := by
  let t : ℝ := (y - a) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hba).2 (by linarith)
  have hy : y = a + (b - a) * t := by
    dsimp [t]
    field_simp [hba.ne']
    ring
  rw [hy, hidentity]
  exact bernsteinValue_nonneg hcoefficients ht0 ht1

/-- A polynomial identity packages the concrete arithmetic part of a
Bernstein certificate. -/
theorem nonneg_on_interval_of_polynomial_identity {n : ℕ}
    {p : ℝ[X]} {coefficients : List ℝ} {a b y : ℝ}
    (hab : a < b) (hya : a ≤ y) (hyb : y ≤ b)
    (hidentity : ∀ t, p.eval (a + (b - a) * t) =
      bernsteinValue n coefficients t)
    (hcoefficients : ∀ j < n + 1, 0 ≤ coefficients.getD j 0) :
    0 ≤ p.eval y :=
  nonneg_on_interval_of_bernstein (F := fun z => p.eval z)
    hab hya hyb hidentity hcoefficients

end TrigonometricBernstein
end CertifiedJL
