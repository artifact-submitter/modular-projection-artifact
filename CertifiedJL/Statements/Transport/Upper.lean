/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.AffineTransport
import CertifiedJL.Statements.L2.Upper
import CertifiedJL.Statements.LInf.Upper
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Shifted upper-tail transports

Deterministic triangle inequalities lift unshifted upper tails to shifted
projection bounds. These transports make no odd-modulus or centered-input
assumption.
-/

namespace CertifiedJL

/-- Exact strict shifted upper squared-norm event at public natural projection and
shift radii. -/
def AffineL2UpperFailureAtRadii (projectedRadius shiftRadius q : ℕ)
    {rows d : ℕ} (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) : Prop :=
  (projectedRadius + shiftRadius) ^ 2 < shiftedModularProjectionSqNorm q shift J w

/-- Exact strict affine upper-coordinate event at public natural projection
and shift radii. -/
def AffineLInfUpperFailureAtRadii (projectedRadius shiftRadius q : ℕ)
    {rows d : ℕ} (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) : Prop :=
  ∃ j, projectedRadius + shiftRadius <
    (centeredMod q (shift j + rowDot J w j)).natAbs

/-- An exact shifted squared-norm overflow is contained in the existing unshifted
L2 upper-failure event. -/
theorem affineL2UpperFailureAtRadii_implies_upperFailure
    (threshold : NonnegativeRatio) {q rows d : ℕ}
    (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) (inputRadius projectedRadius shiftRadius : ℕ)
    (hinput : sqNorm w ≤ inputRadius ^ 2)
    (hprojected : threshold.numerator * inputRadius ^ 2 ≤
      threshold.denominator * projectedRadius ^ 2)
    (hshift : ∑ j, (centeredMod q (shift j)).natAbs ^ 2 ≤ shiftRadius ^ 2)
    (hfailure : AffineL2UpperFailureAtRadii projectedRadius shiftRadius q
      shift w J) :
    L2UpperFailure threshold q w J := by
  by_contra h
  simp only [L2UpperFailure, not_lt] at h
  have hmodScaled : threshold.denominator * modularProjectionSqNorm q J w ≤
      threshold.denominator * projectedRadius ^ 2 :=
    h.trans (Nat.mul_le_mul_left _ hinput) |>.trans hprojected
  have hmod : modularProjectionSqNorm q J w ≤ projectedRadius ^ 2 :=
    Nat.le_of_mul_le_mul_left hmodScaled threshold.denominator_pos
  exact (Nat.not_lt_of_ge
    (shiftedModularProjectionSqNorm_le_add_sq shift J w projectedRadius shiftRadius
      hmod hshift)) hfailure

/-- Every modular L2 upper endpoint lifts to an affine exact-radius endpoint.
No parity, centered-input, or modulus-margin assumption is introduced. -/
theorem L2UpperTailAt.affine_radii
    {parameters : L2UpperParameters} {budget : ENNReal}
    (h : L2UpperTailAt parameters budget)
    (q d : ℕ) (w : Fin d → ℤ)
    (shift : Fin parameters.rows → ℤ)
    (inputRadius projectedRadius shiftRadius : ℕ)
    (hinput : sqNorm w ≤ inputRadius ^ 2)
    (hprojected : parameters.threshold.numerator * inputRadius ^ 2 ≤
      parameters.threshold.denominator * projectedRadius ^ 2)
    (hshift : ∑ j, (centeredMod q (shift j)).natAbs ^ 2 ≤ shiftRadius ^ 2) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineL2UpperFailureAtRadii projectedRadius shiftRadius q shift w) <
        budget := by
  exact (eventProbability_mono _ fun J hJ =>
    affineL2UpperFailureAtRadii_implies_upperFailure parameters.threshold
      shift w J inputRadius projectedRadius shiftRadius hinput hprojected
      hshift hJ).trans_lt (h q d w)

/-- An exact affine coordinate overflow is contained in the existing
unshifted L-infinity upper-failure event. -/
theorem affineLInfUpperFailureAtRadii_implies_upperFailure
    (parameters : LInfUpperParameters) {q d : ℕ}
    (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ)
    (inputRadius projectedRadius shiftRadius : ℕ)
    (hinput : sqNorm w ≤ inputRadius ^ 2)
    (hprojected : parameters.coordinateThreshold.numerator * inputRadius ≤
      parameters.coordinateThreshold.denominator * projectedRadius)
    (hshift : ∀ j, (centeredMod q (shift j)).natAbs ≤ shiftRadius)
    (hfailure : AffineLInfUpperFailureAtRadii projectedRadius shiftRadius q
      shift w J) :
    LInfUpperFailure parameters q w J := by
  obtain ⟨j, hj⟩ := hfailure
  refine ⟨j, ?_⟩
  have hunshifted : projectedRadius <
      (centeredMod q (rowDot J w j)).natAbs := by
    by_contra h
    simp only [not_lt] at h
    exact (Nat.not_lt_of_ge <| (centeredMod_natAbs_add_le q _ _).trans
      (by simpa [add_comm] using Nat.add_le_add (hshift j) h)) hj
  have hsqrt : sqNorm w ≤ inputRadius ^ 2 := hinput
  have hleft : parameters.coordinateThreshold.numerator ^ 2 * sqNorm w ≤
      (parameters.coordinateThreshold.denominator * projectedRadius) ^ 2 := by
    calc
      _ ≤ parameters.coordinateThreshold.numerator ^ 2 * inputRadius ^ 2 :=
        Nat.mul_le_mul_left _ hsqrt
      _ = (parameters.coordinateThreshold.numerator * inputRadius) ^ 2 := by ring
      _ ≤ (parameters.coordinateThreshold.denominator * projectedRadius) ^ 2 :=
        Nat.pow_le_pow_left hprojected 2
  exact hleft.trans_lt (by
    have hp := pow_lt_pow_left₀ hunshifted (Nat.zero_le projectedRadius)
      (by decide : 2 ≠ 0)
    calc
      (parameters.coordinateThreshold.denominator * projectedRadius) ^ 2 =
          parameters.coordinateThreshold.denominator ^ 2 * projectedRadius ^ 2 := by ring
      _ < parameters.coordinateThreshold.denominator ^ 2 *
          (centeredMod q (rowDot J w j)).natAbs ^ 2 :=
        Nat.mul_lt_mul_of_pos_left hp
          (pow_pos parameters.coordinateThreshold.denominator_pos 2)
      _ = _ := rfl)

/-- Every modular L-infinity upper endpoint lifts to an affine exact-radius
endpoint, with no lower-tail hypotheses. -/
theorem LInfUpperTailAt.affine_radii
    {parameters : LInfUpperParameters} {budget : ENNReal}
    (h : LInfUpperTailAt parameters budget)
    (q d : ℕ) (w : Fin d → ℤ)
    (shift : Fin parameters.rows → ℤ)
    (inputRadius projectedRadius shiftRadius : ℕ)
    (hinput : sqNorm w ≤ inputRadius ^ 2)
    (hprojected : parameters.coordinateThreshold.numerator * inputRadius ≤
      parameters.coordinateThreshold.denominator * projectedRadius)
    (hshift : ∀ j, (centeredMod q (shift j)).natAbs ≤ shiftRadius) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineLInfUpperFailureAtRadii projectedRadius shiftRadius q shift w) <
        budget := by
  exact (eventProbability_mono _ fun J hJ =>
    affineLInfUpperFailureAtRadii_implies_upperFailure parameters shift w J
      inputRadius projectedRadius shiftRadius hinput hprojected hshift hJ).trans_lt
    (h q d w)

/-- Strict affine L2 upper overflow at the unchanged real endpoint plus the
exact centered-shift Euclidean norm. -/
def AffineL2UpperFailureWithShift (threshold : NonnegativeRatio) (q : ℕ)
    {rows d : ℕ} (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) : Prop :=
  Real.sqrt (shiftedModularProjectionSqNorm q shift J w) >
    Real.sqrt threshold.toReal * Real.sqrt (sqNorm w) +
      Real.sqrt (∑ j, (centeredMod q (shift j)).natAbs ^ 2)

/-- Affine modular L2 upper-tail schema at the original endpoint plus the
exact centered-shift norm. -/
def AffineL2UpperTailAt (parameters : L2UpperParameters)
    (budget : ENNReal) : Prop :=
  -- Fix the modulus, source dimension, source vector, and arbitrary shift.
  ∀ (q d : ℕ) (w : Fin d → ℤ) (shift : Fin parameters.rows → ℤ),
    -- Sample `J` only after the shift is fixed; strict shifted overflow must
    -- have probability below `budget`.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineL2UpperFailureWithShift parameters.threshold q shift w) < budget

/-- The real Euclidean affine overflow is contained in the original exact
natural upper-failure event. -/
theorem affineL2UpperFailureWithShift_implies_upperFailure
    (threshold : NonnegativeRatio) {q rows d : ℕ}
    (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ)
    (hfailure : AffineL2UpperFailureWithShift threshold q shift w J) :
    L2UpperFailure threshold q w J := by
  by_contra h
  simp only [L2UpperFailure, not_lt] at h
  have hratio0 : 0 ≤ threshold.toReal := by
    unfold NonnegativeRatio.toReal
    positivity
  have hmod : (modularProjectionSqNorm q J w : ℝ) ≤
      threshold.toReal * sqNorm w := by
    unfold NonnegativeRatio.toReal
    have hc : (threshold.denominator : ℝ) * modularProjectionSqNorm q J w ≤
        threshold.numerator * sqNorm w := by exact_mod_cast h
    rw [show (threshold.numerator : ℝ) / threshold.denominator * sqNorm w =
      (threshold.numerator * sqNorm w) / threshold.denominator by ring]
    apply (le_div_iff₀ (by exact_mod_cast threshold.denominator_pos)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  have hsqrt := Real.sqrt_le_sqrt hmod
  rw [Real.sqrt_mul hratio0] at hsqrt
  exact (not_lt_of_ge <| (sqrt_shiftedModularProjectionSqNorm_le shift J w).trans
    (by linarith)) hfailure

/-- At zero shift, the real affine L2 overflow is exactly the original
cross-multiplied modular upper-failure event. -/
@[simp]
theorem affineL2UpperFailureWithShift_zeroShift
    (threshold : NonnegativeRatio) (q : ℕ) {rows d : ℕ}
    (w : Fin d → ℤ) (J : Matrix (Fin rows) (Fin d) ℤ) :
    AffineL2UpperFailureWithShift threshold q (fun _ => 0) w J ↔
      L2UpperFailure threshold q w J := by
  constructor
  · exact affineL2UpperFailureWithShift_implies_upperFailure threshold
      (fun _ => 0) w J
  · intro h
    unfold AffineL2UpperFailureWithShift
    rw [shiftedModularProjectionSqNorm_zero]
    have hzero : (centeredMod q 0).natAbs = 0 := by
      have hz := centeredMod_natAbs_le q 0
      omega
    have hratio : threshold.toReal * (sqNorm w : ℝ) <
        modularProjectionSqNorm q J w := by
      unfold L2UpperFailure at h
      have hcast : (threshold.numerator : ℝ) * sqNorm w <
          threshold.denominator * modularProjectionSqNorm q J w := by
        exact_mod_cast h
      unfold NonnegativeRatio.toReal
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by exact_mod_cast threshold.denominator_pos)).2
      simpa [mul_comm] using hcast
    have hsqrt := Real.sqrt_lt_sqrt
      (mul_nonneg (by unfold NonnegativeRatio.toReal; positivity) (by positivity))
      hratio
    rw [Real.sqrt_mul (by unfold NonnegativeRatio.toReal; positivity)] at hsqrt
    simpa [hzero] using hsqrt

/-- Every exact modular L2 upper endpoint has a no-rounding affine norm
wrapper.  It inherits the same strict budget and no lower-tail assumptions. -/
theorem L2UpperTailAt.affine_norm
    {parameters : L2UpperParameters} {budget : ENNReal}
    (h : L2UpperTailAt parameters budget)
    (q d : ℕ) (w : Fin d → ℤ) (shift : Fin parameters.rows → ℤ) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineL2UpperFailureWithShift parameters.threshold q shift w) < budget := by
  exact (eventProbability_mono _ fun J hJ =>
    affineL2UpperFailureWithShift_implies_upperFailure parameters.threshold
      shift w J hJ).trans_lt (h q d w)

/-- Package the pointwise no-rounding L2 affine adapter as a reusable tail
schema. -/
theorem L2UpperTailAt.to_affine
    {parameters : L2UpperParameters} {budget : ENNReal}
    (h : L2UpperTailAt parameters budget) :
    AffineL2UpperTailAt parameters budget := by
  intro q d w shift
  exact h.affine_norm q d w shift

/-- An affine L2 upper-tail theorem specializes at zero shift to the original
unshifted theorem. -/
theorem AffineL2UpperTailAt.to_unshifted
    {parameters : L2UpperParameters} {budget : ENNReal}
    (h : AffineL2UpperTailAt parameters budget) :
    L2UpperTailAt parameters budget := by
  intro q d w
  rw [eventProbability_congr
    (parameters.distribution.matrixPMF parameters.rows d)
    (event' := AffineL2UpperFailureWithShift parameters.threshold q
      (fun _ => 0) w)
    (fun J => (affineL2UpperFailureWithShift_zeroShift
      parameters.threshold q w J).symm)]
  exact h q d w (fun _ => 0)

/-- Affine L2 upper tails have exactly the same admissible budgets as their
unshifted specialization. -/
theorem affineL2UpperTailAt_iff
    {parameters : L2UpperParameters} {budget : ENNReal} :
    AffineL2UpperTailAt parameters budget ↔
      L2UpperTailAt parameters budget :=
  ⟨AffineL2UpperTailAt.to_unshifted, L2UpperTailAt.to_affine⟩

/-- Strict affine L-infinity overflow at the unchanged real endpoint plus
the exact maximum centered shift coordinate. -/
def AffineLInfUpperFailureWithShift (parameters : LInfUpperParameters)
    (q : ℕ) {d : ℕ} (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ) : Prop :=
  ∃ j, ((centeredMod q (shift j + rowDot J w j)).natAbs : ℝ) >
    parameters.coordinateThreshold.toReal * Real.sqrt (sqNorm w) +
      centeredShiftLInf q shift

/-- Affine modular L-infinity upper-tail schema at the original endpoint plus
the exact maximum centered-shift coordinate. -/
def AffineLInfUpperTailAt (parameters : LInfUpperParameters)
    (budget : ENNReal) : Prop :=
  -- Fix the modulus, source dimension, source vector, and arbitrary shift.
  ∀ (q d : ℕ) (w : Fin d → ℤ) (shift : Fin parameters.rows → ℤ),
    -- Sample `J` only after the shift is fixed; the event that some shifted
    -- coordinate strictly exceeds the cap must have probability below `budget`.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineLInfUpperFailureWithShift parameters q shift w) < budget

/-- The real affine coordinate overflow is contained in the original exact
natural L-infinity upper-failure event. -/
theorem affineLInfUpperFailureWithShift_implies_upperFailure
    (parameters : LInfUpperParameters) {q d : ℕ}
    (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ)
    (hfailure : AffineLInfUpperFailureWithShift parameters q shift w J) :
    LInfUpperFailure parameters q w J := by
  obtain ⟨j, hj⟩ := hfailure
  refine ⟨j, ?_⟩
  by_contra h
  simp only [not_lt] at h
  have hcoord : ((centeredMod q (rowDot J w j)).natAbs : ℝ) ≤
      parameters.coordinateThreshold.toReal * Real.sqrt (sqNorm w) := by
    have hc : (parameters.coordinateThreshold.denominator : ℝ) ^ 2 *
        ((centeredMod q (rowDot J w j)).natAbs : ℝ) ^ 2 ≤
      (parameters.coordinateThreshold.numerator : ℝ) ^ 2 * sqNorm w := by
      exact_mod_cast h
    have hsquare :
        ((parameters.coordinateThreshold.denominator : ℝ) *
          (centeredMod q (rowDot J w j)).natAbs) ^ 2 ≤
        ((parameters.coordinateThreshold.numerator : ℝ) *
          Real.sqrt (sqNorm w)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ sqNorm w)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hc
    have hlinear : (parameters.coordinateThreshold.denominator : ℝ) *
        (centeredMod q (rowDot J w j)).natAbs ≤
      parameters.coordinateThreshold.numerator * Real.sqrt (sqNorm w) :=
      (sq_le_sq₀ (by positivity) (by positivity)).1 hsquare
    unfold NonnegativeRatio.toReal
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by exact_mod_cast
      parameters.coordinateThreshold.denominator_pos)).2
      (by simpa [mul_comm] using hlinear)
  have htri : ((centeredMod q (shift j + rowDot J w j)).natAbs : ℝ) ≤
      (centeredMod q (shift j)).natAbs +
        (centeredMod q (rowDot J w j)).natAbs := by
    exact_mod_cast centeredMod_natAbs_add_le q _ _
  have hshift : ((centeredMod q (shift j)).natAbs : ℝ) ≤
      centeredShiftLInf q shift := by
    exact_mod_cast centeredMod_shift_le_centeredShiftLInf shift j
  linarith

/-- At zero shift, the real affine L-infinity overflow is exactly the original
squared cross-multiplied modular upper-failure event. -/
@[simp]
theorem affineLInfUpperFailureWithShift_zeroShift
    (parameters : LInfUpperParameters) (q : ℕ) {d : ℕ}
    (w : Fin d → ℤ)
    (J : Matrix (Fin parameters.rows) (Fin d) ℤ) :
    AffineLInfUpperFailureWithShift parameters q (fun _ => 0) w J ↔
      LInfUpperFailure parameters q w J := by
  constructor
  · exact affineLInfUpperFailureWithShift_implies_upperFailure parameters
      (fun _ => 0) w J
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hzero : (centeredMod q 0).natAbs = 0 := by
      have hz := centeredMod_natAbs_le q 0
      omega
    have hsquare :
        ((parameters.coordinateThreshold.numerator : ℝ) *
            Real.sqrt (sqNorm w)) ^ 2 <
          ((parameters.coordinateThreshold.denominator : ℝ) *
            (centeredMod q (rowDot J w j)).natAbs) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ sqNorm w)]
      exact_mod_cast hj
    have hlinear :
        (parameters.coordinateThreshold.numerator : ℝ) *
            Real.sqrt (sqNorm w) <
          parameters.coordinateThreshold.denominator *
            (centeredMod q (rowDot J w j)).natAbs :=
      (sq_lt_sq₀ (by positivity) (by positivity)).1 hsquare
    have hratio : parameters.coordinateThreshold.toReal *
        Real.sqrt (sqNorm w) <
          (centeredMod q (rowDot J w j)).natAbs := by
      unfold NonnegativeRatio.toReal
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ (by exact_mod_cast
        parameters.coordinateThreshold.denominator_pos)).2
        (by simpa [mul_comm] using hlinear)
    have hshiftzero : centeredShiftLInf q
        (fun _ : Fin parameters.rows => 0) = 0 := by
      unfold centeredShiftLInf
      exact Finset.sup_eq_zero.mpr (fun _ _ => hzero)
    simpa [hzero, hshiftzero] using hratio

/-- Every exact modular L-infinity upper endpoint has a no-rounding affine
norm wrapper with the same strict budget and no lower-tail assumptions. -/
theorem LInfUpperTailAt.affine_norm
    {parameters : LInfUpperParameters} {budget : ENNReal}
    (h : LInfUpperTailAt parameters budget)
    (q d : ℕ) (w : Fin d → ℤ) (shift : Fin parameters.rows → ℤ) :
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineLInfUpperFailureWithShift parameters q shift w) < budget := by
  exact (eventProbability_mono _ fun J hJ =>
    affineLInfUpperFailureWithShift_implies_upperFailure parameters shift w J
      hJ).trans_lt (h q d w)

/-- Package the pointwise no-rounding L-infinity affine adapter as a reusable
tail schema. -/
theorem LInfUpperTailAt.to_affine
    {parameters : LInfUpperParameters} {budget : ENNReal}
    (h : LInfUpperTailAt parameters budget) :
    AffineLInfUpperTailAt parameters budget := by
  intro q d w shift
  exact h.affine_norm q d w shift

/-- An affine L-infinity upper-tail theorem specializes at zero shift to the
original unshifted theorem. -/
theorem AffineLInfUpperTailAt.to_unshifted
    {parameters : LInfUpperParameters} {budget : ENNReal}
    (h : AffineLInfUpperTailAt parameters budget) :
    LInfUpperTailAt parameters budget := by
  intro q d w
  rw [eventProbability_congr
    (parameters.distribution.matrixPMF parameters.rows d)
    (event' := AffineLInfUpperFailureWithShift parameters q (fun _ => 0) w)
    (fun J => (affineLInfUpperFailureWithShift_zeroShift parameters q w J).symm)]
  exact h q d w (fun _ => 0)

/-- Affine L-infinity upper tails have exactly the same admissible budgets as
their unshifted specialization. -/
theorem affineLInfUpperTailAt_iff
    {parameters : LInfUpperParameters} {budget : ENNReal} :
    AffineLInfUpperTailAt parameters budget ↔
      LInfUpperTailAt parameters budget :=
  ⟨AffineLInfUpperTailAt.to_unshifted, LInfUpperTailAt.to_affine⟩

end CertifiedJL
