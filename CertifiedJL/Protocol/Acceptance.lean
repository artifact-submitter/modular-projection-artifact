/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.AffineTransport
import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.LInf.Lower.Affine
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Closed-acceptance adapters

These adapters turn closed real acceptance radii into the exact strict
lower-failure events used by the public tail statements. Each conversion
displays the strict numerical headroom it requires. They are deterministic
event inclusions and numerical approximation lemmas; they do not model a
protocol transcript or a zero-knowledge argument.
-/

namespace CertifiedJL

/-- Closed real L2 acceptance at radius `A`. -/
def AffineL2ClosedAcceptance (A : ℝ) (q : ℕ) {rows d : ℕ}
    (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) : Prop :=
  (shiftedModularProjectionSqNorm q shift J w : ℝ) ≤ A ^ 2

/-- Closed real L-infinity acceptance at radius `A`. -/
def AffineLInfClosedAcceptance (A : ℝ) (q : ℕ) {rows d : ℕ}
    (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) : Prop :=
  ∀ j, ((centeredMod q (shift j + rowDot J w j)).natAbs : ℝ) ≤ A

/-- A closed real L2 acceptance event lies in the strict integer lower
failure event whenever `A² < L b²`, stated without rounding `A`. -/
theorem affineL2ClosedAcceptance_implies_lowerFailure
    (squaredNormFloor : NonnegativeRatio) (A : ℝ) (inputThreshold q : ℕ)
    {rows d : ℕ} (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ)
    (hfit : squaredNormFloor.denominator * A ^ 2 <
      squaredNormFloor.numerator * (inputThreshold : ℝ) ^ 2)
    (haccept : AffineL2ClosedAcceptance A q shift w J) :
    AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q shift w J := by
  unfold AffineL2ClosedAcceptance at haccept
  unfold AffineL2ThresholdLowerFailure
  exact_mod_cast (calc
    (squaredNormFloor.denominator : ℝ) * shiftedModularProjectionSqNorm q shift J w ≤
        squaredNormFloor.denominator * A ^ 2 := by gcongr
    _ < squaredNormFloor.numerator * (inputThreshold : ℝ) ^ 2 := hfit)

/-- Public probability adapter for a closed real L2 acceptance radius. -/
theorem AffineL2ThresholdLowerTailAt.closedAcceptance
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    (h : AffineL2ThresholdLowerTailAt parameters budget)
    (A : ℝ) (q d inputThreshold : ℕ) (w : Fin d → ℤ)
    (shift : Fin parameters.rows → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hpositive : 0 < inputThreshold)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hmodulus : InputThresholdWithinModulus parameters.modulusMargin q
      inputThreshold)
    (hfit : parameters.squaredNormFloor.denominator * A ^ 2 <
      parameters.squaredNormFloor.numerator * (inputThreshold : ℝ) ^ 2) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineL2ClosedAcceptance A q shift w) < budget := by
  exact (eventProbability_mono _ fun J hJ =>
    affineL2ClosedAcceptance_implies_lowerFailure parameters.squaredNormFloor A
      inputThreshold q shift w J hfit hJ).trans_lt
    (h q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus)

/-- Odd-denominator Archimedean approximation.  Between two nonnegative real
radii one can place an integer after multiplying both by one common odd
natural scale. -/
theorem exists_odd_scale_nat_between {A B : ℝ} (hA : 0 ≤ A) (hAB : A < B) :
    ∃ (k b : ℕ), Odd k ∧ 0 < k ∧ (k : ℝ) * A < b ∧ (b : ℝ) ≤ k * B := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hAB)
  let k : ℕ := 2 * (n + 1) + 1
  let b : ℕ := ⌊(k : ℝ) * A⌋₊ + 1
  have hkpos : 0 < k := by simp [k]
  have hkgap : 1 < (k : ℝ) * (B - A) := by
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    have hone : 1 < (n + 1 : ℝ) * (B - A) := by
      have := (div_lt_iff₀ hnpos).1 hn
      nlinarith
    have hnk : (n + 1 : ℝ) ≤ k := by
      norm_num [k]
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    nlinarith [mul_le_mul_of_nonneg_right hnk (sub_pos.2 hAB).le]
  have hkA0 : 0 ≤ (k : ℝ) * A := mul_nonneg (by positivity) hA
  refine ⟨k, b, ?_, hkpos, ?_, ?_⟩
  · exact ⟨n + 1, by simp [k]⟩
  · simpa [b] using Nat.lt_floor_add_one ((k : ℝ) * A)
  · have hfloor := Nat.floor_le hkA0
    have hb : (b : ℝ) ≤ (k : ℝ) * A + 1 := by
      simp only [b, Nat.cast_add, Nat.cast_one]
      linarith
    nlinarith

/-- Odd-scale approximation specialized to a positive coordinate cap.  The
strict real headroom `A < c B` produces a positive integer threshold `b`
between the scaled acceptance radius and the scaled norm threshold. -/
theorem exists_odd_scale_nat_of_lInf_headroom
    (cap : NonnegativeRatio) {A B : ℝ}
    (hA : 0 ≤ A) (_hB : 0 < B) (hcap : 0 < cap.numerator)
    (hfit : A < cap.toReal * B) :
    ∃ (k b : ℕ), Odd k ∧ 0 < k ∧ 0 < b ∧
      (b : ℝ) ≤ k * B ∧ (k : ℝ) * A < cap.toReal * b := by
  have hcapReal : 0 < cap.toReal := by
    unfold NonnegativeRatio.toReal
    exact div_pos (by exact_mod_cast hcap)
      (by exact_mod_cast cap.denominator_pos)
  have hratio0 : 0 ≤ A / cap.toReal := div_nonneg hA hcapReal.le
  have hratio_lt : A / cap.toReal < B := by
    exact (div_lt_iff₀ hcapReal).2 (by simpa [mul_comm] using hfit)
  obtain ⟨k, b, hkodd, hkpos, hbLower, hbUpper⟩ :=
    exists_odd_scale_nat_between hratio0 hratio_lt
  have hbpos : 0 < b := by
    have hleft : 0 ≤ (k : ℝ) * (A / cap.toReal) :=
      mul_nonneg (by positivity) hratio0
    have : (0 : ℝ) < b := hleft.trans_lt hbLower
    exact_mod_cast this
  have hscaled : (k : ℝ) * A < cap.toReal * b := by
    have hmul := mul_lt_mul_of_pos_left hbLower hcapReal
    calc
      (k : ℝ) * A = cap.toReal * ((k : ℝ) * (A / cap.toReal)) := by
        field_simp
      _ < cap.toReal * b := hmul
  exact ⟨k, b, hkodd, hkpos, hbpos, hbUpper, hscaled⟩

/-- A closed affine L-infinity acceptance event at radius `A` becomes the
exact coordinate-cap event after a common positive odd scaling, provided the
scaled integer threshold lies strictly above `k A / c`. -/
theorem affineLInfClosedAcceptance_oddScale_implies_smallProjection
    (parameters : LInfThresholdLowerParameters) (A : ℝ) (q k b : ℕ)
    {d : ℕ} (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ)
    (hk : Odd k) (hq : Odd q)
    (hfit : (k : ℝ) * A < parameters.coordinateCap.toReal * b)
    (haccept : AffineLInfClosedAcceptance A q shift w J) :
    AffineLInfThresholdSmallProjection parameters b (k * q)
      (fun j => (k : ℤ) * shift j) (fun i => (k : ℤ) * w i) J := by
  intro j
  have hrow : rowDot J (fun i => (k : ℤ) * w i) j =
      (k : ℤ) * rowDot J w j := rowDot_natCast_mul k J w j
  have hcoord :
      (centeredMod (k * q)
          ((k : ℤ) * shift j + rowDot J (fun i => (k : ℤ) * w i) j)).natAbs =
        k * (centeredMod q (shift j + rowDot J w j)).natAbs := by
    rw [hrow, ← mul_add, centeredMod_odd_mul k q hk hq, natAbs_natCast_mul]
  have hscaledAcceptance :
      ((centeredMod (k * q)
          ((k : ℤ) * shift j + rowDot J (fun i => (k : ℤ) * w i) j)).natAbs : ℝ) ≤
        (k : ℝ) * A := by
    rw [hcoord]
    push_cast
    exact mul_le_mul_of_nonneg_left (haccept j) (by positivity)
  have hcrossReal : (parameters.coordinateCap.denominator : ℝ) *
      (centeredMod (k * q)
        ((k : ℤ) * shift j + rowDot J (fun i => (k : ℤ) * w i) j)).natAbs ≤
      parameters.coordinateCap.numerator * b := by
    apply le_of_lt
    calc
      _ ≤ parameters.coordinateCap.denominator * ((k : ℝ) * A) := by
        gcongr
      _ < parameters.coordinateCap.denominator *
          (parameters.coordinateCap.toReal * b) := by
        exact mul_lt_mul_of_pos_left hfit
          (by exact_mod_cast parameters.coordinateCap.denominator_pos)
      _ = parameters.coordinateCap.numerator * b := by
        unfold NonnegativeRatio.toReal
        field_simp [ne_of_gt parameters.coordinateCap.denominator_pos]
  have hcrossNat : parameters.coordinateCap.denominator *
      (centeredMod (k * q)
        ((k : ℤ) * shift j + rowDot J (fun i => (k : ℤ) * w i) j)).natAbs ≤
      parameters.coordinateCap.numerator * b := by
    exact_mod_cast hcrossReal
  have hsquare := Nat.pow_le_pow_left hcrossNat 2
  simpa [mul_pow] using hsquare

/-- The square-gap form of odd scaled approximation used by structured real
thresholds.  It explicitly produces the integer threshold used in the
scaled-modulus application. -/
theorem exists_odd_scale_nat_of_sq_lt
    (squaredNormFloor : NonnegativeRatio) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hnum : 0 < squaredNormFloor.numerator)
    (hfit : squaredNormFloor.denominator * A ^ 2 <
      squaredNormFloor.numerator * B ^ 2) :
    ∃ (k b : ℕ), Odd k ∧ 0 < k ∧ (b : ℝ) ≤ k * B ∧
      (squaredNormFloor.denominator : ℝ) * ((k : ℝ) * A) ^ 2 <
        squaredNormFloor.numerator * (b : ℝ) ^ 2 := by
  let R : ℝ := Real.sqrt
    ((squaredNormFloor.denominator : ℝ) / squaredNormFloor.numerator) * A
  have hR0 : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) hA
  have hratio0 : 0 ≤
      (squaredNormFloor.denominator : ℝ) / squaredNormFloor.numerator := by positivity
  have hRsq : R ^ 2 =
      (squaredNormFloor.denominator : ℝ) / squaredNormFloor.numerator * A ^ 2 := by
    simp only [R, mul_pow, Real.sq_sqrt hratio0]
  have hRlt : R < B := by
    have : R ^ 2 < B ^ 2 := by
      rw [hRsq]
      rw [show (squaredNormFloor.denominator : ℝ) /
          squaredNormFloor.numerator * A ^ 2 =
        (squaredNormFloor.denominator * A ^ 2) / squaredNormFloor.numerator by ring]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) <
        squaredNormFloor.numerator)).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfit
    nlinarith [sq_nonneg (R + B)]
  obtain ⟨k, b, hkodd, hkpos, hkbLower, hkbUpper⟩ :=
    exists_odd_scale_nat_between hR0 hRlt
  refine ⟨k, b, hkodd, hkpos, hkbUpper, ?_⟩
  have hsq : ((k : ℝ) * R) ^ 2 < (b : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k) hR0]
  rw [mul_pow, hRsq] at hsq
  have hnumR : (0 : ℝ) < squaredNormFloor.numerator := by positivity
  calc
    (squaredNormFloor.denominator : ℝ) * ((k : ℝ) * A) ^ 2 =
        squaredNormFloor.numerator *
          ((k : ℝ) ^ 2 *
            ((squaredNormFloor.denominator : ℝ) / squaredNormFloor.numerator * A ^ 2)) := by
      field_simp
    _ < squaredNormFloor.numerator * (b : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_left hsq hnumR

/-- Structured closed L2 acceptance with a genuinely real public threshold.
The proof scales the odd modulus and uses an explicitly constructed integer
approximant; it does not round the original block threshold. -/
theorem AffineL2ThresholdLowerTailAt.closedAcceptance_realThreshold
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    (h : AffineL2ThresholdLowerTailAt parameters budget)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hnum : 0 < parameters.squaredNormFloor.numerator)
    (q d : ℕ) (w : Fin d → ℤ) (shift : Fin parameters.rows → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : B ^ 2 ≤ sqNorm w)
    (hmodulus : parameters.modulusMargin.numerator * B ≤
      parameters.modulusMargin.denominator * q)
    (hfit : parameters.squaredNormFloor.denominator * A ^ 2 <
      parameters.squaredNormFloor.numerator * B ^ 2) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineL2ClosedAcceptance A q shift w) < budget := by
  obtain ⟨k, b, hkodd, hkpos, hbB, hscaledFit⟩ :=
    exists_odd_scale_nat_of_sq_lt parameters.squaredNormFloor hA hB hnum hfit
  have hbpos : 0 < b := by
    have hleft0 : (0 : ℝ) ≤ parameters.squaredNormFloor.denominator *
        ((k : ℝ) * A) ^ 2 := by positivity
    have hbSq : (0 : ℝ) < (b : ℝ) ^ 2 := by
      have hnumReal : (0 : ℝ) < parameters.squaredNormFloor.numerator := by positivity
      nlinarith
    exact Nat.pos_of_ne_zero fun hb0 => by subst b; norm_num at hbSq
  have hqk : Odd (k * q) := hkodd.mul hq
  have hcenteredk := hcentered.odd_mul k hkodd hq
  have hnormk : InputThresholdAtMostNorm b (fun i => (k : ℤ) * w i) := by
    unfold InputThresholdAtMostNorm
    rw [sqNorm_natCast_mul]
    have hreal : (b : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * sqNorm w := by
      calc
        (b : ℝ) ^ 2 ≤ ((k : ℝ) * B) ^ 2 :=
          (sq_le_sq₀ (by positivity) (mul_nonneg (by positivity) hB.le)).2 hbB
        _ ≤ (k : ℝ) ^ 2 * sqNorm w := by
          rw [mul_pow]
          gcongr
    exact_mod_cast hreal
  have hmodulusk : InputThresholdWithinModulus parameters.modulusMargin
      (k * q) b := by
    unfold InputThresholdWithinModulus
    have hm0 : (0 : ℝ) ≤ parameters.modulusMargin.numerator := by positivity
    have hreal : (parameters.modulusMargin.numerator : ℝ) * b ≤
        parameters.modulusMargin.denominator * (k * q : ℕ) := by
      calc
        _ ≤ parameters.modulusMargin.numerator * ((k : ℝ) * B) := by gcongr
        _ = (k : ℝ) * (parameters.modulusMargin.numerator * B) := by ring
        _ ≤ k * (parameters.modulusMargin.denominator * q) := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast hreal
  have hsource := h (k * q) d (fun i => (k : ℤ) * w i) b
    (fun j => (k : ℤ) * shift j) hqk hcenteredk hbpos hnormk hmodulusk
  apply (eventProbability_mono _ ?_).trans_lt hsource
  intro J haccept
  unfold AffineL2ClosedAcceptance at haccept
  unfold AffineL2ThresholdLowerFailure
  rw [shiftedModularProjectionSqNorm_odd_mul k q hkodd hq shift J w]
  have hsquaredNorm : (parameters.squaredNormFloor.denominator : ℝ) *
      ((k : ℝ) ^ 2 * shiftedModularProjectionSqNorm q shift J w) ≤
      parameters.squaredNormFloor.denominator * ((k : ℝ) * A) ^ 2 := by
    rw [mul_pow]
    gcongr
  exact_mod_cast hsquaredNorm.trans_lt hscaledFit

/-- Unshifted structured closed L2 acceptance with a genuinely real public
threshold.  This is the zero-shift analogue used by applications of the
original L2 lower-tail schema. -/
theorem L2ThresholdLowerTailAt.closedAcceptance_realThreshold
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    (h : L2ThresholdLowerTailAt parameters budget)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hnum : 0 < parameters.squaredNormFloor.numerator)
    (q d : ℕ) (w : Fin d → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : B ^ 2 ≤ sqNorm w)
    (hmodulus : parameters.modulusMargin.numerator * B ≤
      parameters.modulusMargin.denominator * q)
    (hfit : parameters.squaredNormFloor.denominator * A ^ 2 <
      parameters.squaredNormFloor.numerator * B ^ 2) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (fun J => (modularProjectionSqNorm q J w : ℝ) ≤ A ^ 2) < budget := by
  obtain ⟨k, b, hkodd, hkpos, hbB, hscaledFit⟩ :=
    exists_odd_scale_nat_of_sq_lt parameters.squaredNormFloor hA hB hnum hfit
  have hbpos : 0 < b := by
    have hleft0 : (0 : ℝ) ≤ parameters.squaredNormFloor.denominator *
        ((k : ℝ) * A) ^ 2 := by positivity
    have hbSq : (0 : ℝ) < (b : ℝ) ^ 2 := by
      have hnumReal : (0 : ℝ) < parameters.squaredNormFloor.numerator := by positivity
      nlinarith
    exact Nat.pos_of_ne_zero fun hb0 => by subst b; norm_num at hbSq
  have hqk : Odd (k * q) := hkodd.mul hq
  have hcenteredk := hcentered.odd_mul k hkodd hq
  have hnormk : InputThresholdAtMostNorm b (fun i => (k : ℤ) * w i) := by
    unfold InputThresholdAtMostNorm
    rw [sqNorm_natCast_mul]
    have hreal : (b : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * sqNorm w := by
      calc
        (b : ℝ) ^ 2 ≤ ((k : ℝ) * B) ^ 2 :=
          (sq_le_sq₀ (by positivity) (mul_nonneg (by positivity) hB.le)).2 hbB
        _ ≤ (k : ℝ) ^ 2 * sqNorm w := by
          rw [mul_pow]
          gcongr
    exact_mod_cast hreal
  have hmodulusk : InputThresholdWithinModulus parameters.modulusMargin
      (k * q) b := by
    unfold InputThresholdWithinModulus
    have hreal : (parameters.modulusMargin.numerator : ℝ) * b ≤
        parameters.modulusMargin.denominator * (k * q : ℕ) := by
      calc
        _ ≤ parameters.modulusMargin.numerator * ((k : ℝ) * B) := by gcongr
        _ = (k : ℝ) * (parameters.modulusMargin.numerator * B) := by ring
        _ ≤ k * (parameters.modulusMargin.denominator * q) := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast hreal
  have hsource := h (k * q) d (fun i => (k : ℤ) * w i) b hqk
    hcenteredk hbpos hnormk hmodulusk
  apply (eventProbability_mono _ ?_).trans_lt hsource
  intro J haccept
  unfold L2ThresholdLowerFailure
  have hscale : modularProjectionSqNorm (k * q) J (fun i => (k : ℤ) * w i) =
      k ^ 2 * modularProjectionSqNorm q J w := by
    simpa [shiftedModularProjectionSqNorm, modularProjectionSqNorm] using
      shiftedModularProjectionSqNorm_odd_mul k q hkodd hq (fun _ => 0) J w
  rw [hscale]
  have hsquaredNorm : (parameters.squaredNormFloor.denominator : ℝ) *
      ((k : ℝ) ^ 2 * modularProjectionSqNorm q J w) ≤
      parameters.squaredNormFloor.denominator * ((k : ℝ) * A) ^ 2 := by
    rw [mul_pow]
    gcongr
  exact_mod_cast hsquaredNorm.trans_lt hscaledFit

/-- Structured affine closed L-infinity acceptance with a genuinely real
public norm threshold.  Strict headroom `A < c B` is preserved by an odd
common scaling, so the original real threshold is never rounded. -/
theorem AffineLInfThresholdLowerTailAt.closedAcceptance_realThreshold
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    (h : AffineLInfThresholdLowerTailAt parameters budget)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hcap : 0 < parameters.coordinateCap.numerator)
    (q d : ℕ) (w : Fin d → ℤ) (shift : Fin parameters.rows → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : B ^ 2 ≤ sqNorm w)
    (hmodulus : parameters.modulusMargin.numerator * B ≤
      parameters.modulusMargin.denominator * q)
    (hfit : A < parameters.coordinateCap.toReal * B) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineLInfClosedAcceptance A q shift w) < budget := by
  obtain ⟨k, b, hkodd, hkpos, hbpos, hbB, hscaledFit⟩ :=
    exists_odd_scale_nat_of_lInf_headroom parameters.coordinateCap hA hB hcap hfit
  have hqk : Odd (k * q) := hkodd.mul hq
  have hcenteredk := hcentered.odd_mul k hkodd hq
  have hnormk : InputThresholdAtMostNorm b (fun i => (k : ℤ) * w i) := by
    unfold InputThresholdAtMostNorm
    rw [sqNorm_natCast_mul]
    have hreal : (b : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * sqNorm w := by
      calc
        (b : ℝ) ^ 2 ≤ ((k : ℝ) * B) ^ 2 :=
          (sq_le_sq₀ (by positivity) (mul_nonneg (by positivity) hB.le)).2 hbB
        _ ≤ (k : ℝ) ^ 2 * sqNorm w := by
          rw [mul_pow]
          gcongr
    exact_mod_cast hreal
  have hmodulusk : InputThresholdWithinModulus parameters.modulusMargin
      (k * q) b := by
    unfold InputThresholdWithinModulus
    have hreal : (parameters.modulusMargin.numerator : ℝ) * b ≤
        parameters.modulusMargin.denominator * (k * q : ℕ) := by
      calc
        _ ≤ parameters.modulusMargin.numerator * ((k : ℝ) * B) := by gcongr
        _ = (k : ℝ) * (parameters.modulusMargin.numerator * B) := by ring
        _ ≤ k * (parameters.modulusMargin.denominator * q) := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast hreal
  have hsource := h (k * q) d (fun i => (k : ℤ) * w i) b
    (fun j => (k : ℤ) * shift j) hqk hcenteredk hbpos hnormk hmodulusk
  apply (eventProbability_mono _ ?_).trans_lt hsource
  intro J haccept
  exact affineLInfClosedAcceptance_oddScale_implies_smallProjection parameters
    A q k b shift w J hkodd hq hscaledFit haccept

/-- Unshifted closed L-infinity acceptance with a genuinely real public norm
threshold.  This is the zero-shift analogue of the affine odd-scale adapter. -/
theorem LInfThresholdLowerTailAt.closedAcceptance_realThreshold
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    (h : LInfThresholdLowerTailAt parameters budget)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hcap : 0 < parameters.coordinateCap.numerator)
    (q d : ℕ) (w : Fin d → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : B ^ 2 ≤ sqNorm w)
    (hmodulus : parameters.modulusMargin.numerator * B ≤
      parameters.modulusMargin.denominator * q)
    (hfit : A < parameters.coordinateCap.toReal * B) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (fun J => ∀ j,
        ((centeredMod q (rowDot J w j)).natAbs : ℝ) ≤ A) < budget := by
  obtain ⟨k, b, hkodd, hkpos, hbpos, hbB, hscaledFit⟩ :=
    exists_odd_scale_nat_of_lInf_headroom parameters.coordinateCap hA hB hcap hfit
  have hqk : Odd (k * q) := hkodd.mul hq
  have hcenteredk := hcentered.odd_mul k hkodd hq
  have hnormk : InputThresholdAtMostNorm b (fun i => (k : ℤ) * w i) := by
    unfold InputThresholdAtMostNorm
    rw [sqNorm_natCast_mul]
    have hreal : (b : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * sqNorm w := by
      calc
        (b : ℝ) ^ 2 ≤ ((k : ℝ) * B) ^ 2 :=
          (sq_le_sq₀ (by positivity) (mul_nonneg (by positivity) hB.le)).2 hbB
        _ ≤ (k : ℝ) ^ 2 * sqNorm w := by
          rw [mul_pow]
          gcongr
    exact_mod_cast hreal
  have hmodulusk : InputThresholdWithinModulus parameters.modulusMargin
      (k * q) b := by
    unfold InputThresholdWithinModulus
    have hreal : (parameters.modulusMargin.numerator : ℝ) * b ≤
        parameters.modulusMargin.denominator * (k * q : ℕ) := by
      calc
        _ ≤ parameters.modulusMargin.numerator * ((k : ℝ) * B) := by gcongr
        _ = (k : ℝ) * (parameters.modulusMargin.numerator * B) := by ring
        _ ≤ k * (parameters.modulusMargin.denominator * q) := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast hreal
  have hsource := h (k * q) d (fun i => (k : ℤ) * w i) b hqk
    hcenteredk hbpos hnormk hmodulusk
  apply (eventProbability_mono _ ?_).trans_lt hsource
  intro J haccept
  rw [← affineLInfThresholdSmallProjection_zeroShift parameters b (k * q)
    (fun i => (k : ℤ) * w i) J]
  apply affineLInfClosedAcceptance_oddScale_implies_smallProjection parameters
    A q k b (fun _ => 0) w J hkodd hq hscaledFit
  intro j
  simpa [AffineLInfClosedAcceptance] using haccept j

/-- Natural threshold selected for a closed real L-infinity acceptance
radius and a positive coordinate cap. -/
noncomputable def closedLInfInputThreshold (cap : NonnegativeRatio) (A : ℝ) : ℕ :=
  max 1 ⌈A / cap.toReal⌉₊

/-- The selected closed L-infinity threshold is positive, including at
`A = 0`. -/
theorem closedLInfInputThreshold_pos (cap : NonnegativeRatio) (A : ℝ) :
    0 < closedLInfInputThreshold cap A := by
  simp [closedLInfInputThreshold]

/-- Closed acceptance at a nonnegative real radius is contained in the exact
coordinate-cap event at `max 1 ceil(A/c)`. -/
theorem affineLInfClosedAcceptance_implies_smallProjection
    (parameters : LInfThresholdLowerParameters) (A : ℝ) (_hA : 0 ≤ A)
    (hcap : 0 < parameters.coordinateCap.numerator) (q : ℕ) {d : ℕ}
    (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ)
    (haccept : AffineLInfClosedAcceptance A q shift w J) :
    AffineLInfThresholdSmallProjection parameters
      (closedLInfInputThreshold parameters.coordinateCap A) q shift w J := by
  intro j
  have hcapReal : 0 < parameters.coordinateCap.toReal := by
    unfold NonnegativeRatio.toReal
    exact div_pos (by exact_mod_cast hcap)
      (by exact_mod_cast parameters.coordinateCap.denominator_pos)
  have hceil : A ≤ parameters.coordinateCap.toReal *
      closedLInfInputThreshold parameters.coordinateCap A := by
    calc
      A = parameters.coordinateCap.toReal *
          (A / parameters.coordinateCap.toReal) := by field_simp
      _ ≤ parameters.coordinateCap.toReal *
          (⌈A / parameters.coordinateCap.toReal⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _
      _ ≤ parameters.coordinateCap.toReal *
          closedLInfInputThreshold parameters.coordinateCap A := by
        gcongr
        exact_mod_cast Nat.le_max_right 1 ⌈A / parameters.coordinateCap.toReal⌉₊
  have hj := (haccept j).trans hceil
  have hcross : (parameters.coordinateCap.denominator : ℝ) *
      (centeredMod q (shift j + rowDot J w j)).natAbs ≤
      parameters.coordinateCap.numerator *
        closedLInfInputThreshold parameters.coordinateCap A := by
    have hdpos : (0 : ℝ) < parameters.coordinateCap.denominator := by
      exact_mod_cast parameters.coordinateCap.denominator_pos
    have hm := mul_le_mul_of_nonneg_left hj hdpos.le
    unfold NonnegativeRatio.toReal at hm
    calc
      _ ≤ parameters.coordinateCap.denominator *
          ((parameters.coordinateCap.numerator : ℝ) /
            parameters.coordinateCap.denominator *
              closedLInfInputThreshold parameters.coordinateCap A) := hm
      _ = _ := by field_simp
  have hcrossNat : parameters.coordinateCap.denominator *
      (centeredMod q (shift j + rowDot J w j)).natAbs ≤
      parameters.coordinateCap.numerator *
        closedLInfInputThreshold parameters.coordinateCap A := by
    exact_mod_cast hcross
  have hsquare := Nat.pow_le_pow_left hcrossNat 2
  simpa [mul_pow] using hsquare

/-- Public closed-acceptance adapter for affine L-infinity lower tails.  The
caller supplies norm and modulus conditions at the explicitly displayed
rounded threshold. -/
theorem AffineLInfThresholdLowerTailAt.closedAcceptance
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    (h : AffineLInfThresholdLowerTailAt parameters budget)
    (A : ℝ) (hA : 0 ≤ A) (hcap : 0 < parameters.coordinateCap.numerator)
    (q d : ℕ) (w : Fin d → ℤ) (shift : Fin parameters.rows → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm
      (closedLInfInputThreshold parameters.coordinateCap A) w)
    (hmodulus : InputThresholdWithinModulus parameters.modulusMargin q
      (closedLInfInputThreshold parameters.coordinateCap A)) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineLInfClosedAcceptance A q shift w) < budget := by
  exact (eventProbability_mono _ fun J hJ =>
    affineLInfClosedAcceptance_implies_smallProjection parameters A hA hcap q
      shift w J hJ).trans_lt
    (h q d w (closedLInfInputThreshold parameters.coordinateCap A) shift hq
      hcentered (closedLInfInputThreshold_pos _ _) hnorm hmodulus)

/-- Unshifted closed-acceptance adapter.  The same `max 1 ceil(A/c)` choice
works at `A = 0`, while using only the original unshifted lower-tail schema. -/
theorem LInfThresholdLowerTailAt.closedAcceptance
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    (h : LInfThresholdLowerTailAt parameters budget)
    (A : ℝ) (hA : 0 ≤ A) (hcap : 0 < parameters.coordinateCap.numerator)
    (q d : ℕ) (w : Fin d → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm
      (closedLInfInputThreshold parameters.coordinateCap A) w)
    (hmodulus : InputThresholdWithinModulus parameters.modulusMargin q
      (closedLInfInputThreshold parameters.coordinateCap A)) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (fun J => ∀ j,
        ((centeredMod q (rowDot J w j)).natAbs : ℝ) ≤ A) < budget := by
  have hsource := h q d w
    (closedLInfInputThreshold parameters.coordinateCap A) hq hcentered
    (closedLInfInputThreshold_pos _ _) hnorm hmodulus
  apply (eventProbability_mono _ ?_).trans_lt hsource
  intro J hJ
  rw [← affineLInfThresholdSmallProjection_zeroShift parameters
    (closedLInfInputThreshold parameters.coordinateCap A) q w J]
  apply affineLInfClosedAcceptance_implies_smallProjection parameters A hA hcap q
    (fun _ => 0) w J
  intro j
  simpa [AffineLInfClosedAcceptance] using hJ j

end CertifiedJL
