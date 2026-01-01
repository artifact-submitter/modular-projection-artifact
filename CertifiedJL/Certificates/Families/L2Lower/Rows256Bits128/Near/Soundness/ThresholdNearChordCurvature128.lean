/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Semiconvex128

/-! # Exact Holder-weight derivatives of the chord central moment

All varying terms in the two exact Gaussian cosine moments are instances of
`exp (-1/2 * (m B + offset)^2)`, where `B^2 = (23/20)(x-a)y`.  Keeping this
closed form makes both derivatives finite algebraic expressions and avoids any
differentiation under an integral.
-/

namespace CertifiedJL
namespace ThresholdNearChord128

/-- One closed exponential mode in the exact Gaussian cosine moments. -/
noncomputable def semanticMode (x a y m offset : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * (offset + m * semanticBFreq x a y) ^ 2)

/-- Exact first derivative of `semanticMode` with respect to `y`. -/
noncomputable def semanticModePrime (x a y m offset : ℝ) : ℝ :=
  semanticMode x a y m offset *
    (-(m * semanticBFreq x a y *
      (m * semanticBFreq x a y + offset)) / (2 * y))

/-- Exact second derivative of `semanticMode` with respect to `y`. -/
noncomputable def semanticModeSecond (x a y m offset : ℝ) : ℝ :=
  semanticMode x a y m offset *
    (((m * semanticBFreq x a y *
        (m * semanticBFreq x a y + offset)) ^ 2 +
      m * semanticBFreq x a y * offset) / (4 * y ^ 2))

theorem semanticBFreq_sq {x a y : ℝ} (hxy : 0 ≤ (23 / 20) * (x - a) * y) :
    semanticBFreq x a y ^ 2 = (23 / 20) * (x - a) * y := by
  simpa only [semanticBFreq] using Real.sq_sqrt hxy

theorem hasDerivAt_semanticBFreq {x a y : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticBFreq x a z)
      (semanticBFreq x a y / (2 * y)) y := by
  have hc : 0 < (23 / 20 : ℝ) * (x - a) := by positivity
  have hcy : (23 / 20 : ℝ) * (x - a) * y ≠ 0 := by positivity
  have hsqrt : 0 < semanticBFreq x a y := by
    exact Real.sqrt_pos.mpr (by positivity)
  have hraw : HasDerivAt
      (fun z : ℝ ↦ Real.sqrt ((23 / 20) * (x - a) * z))
      (1 / (2 * Real.sqrt ((23 / 20) * (x - a) * y)) *
        ((23 / 20) * (x - a))) y := by
    convert (Real.hasDerivAt_sqrt hcy |>.comp y
      (hasDerivAt_const_mul ((23 / 20 : ℝ) * (x - a)))) using 1
    all_goals rfl
  apply hraw.congr_deriv
  change 1 / (2 * semanticBFreq x a y) * ((23 / 20) * (x - a)) =
    semanticBFreq x a y / (2 * y)
  field_simp [hy.ne', hsqrt.ne']
  rw [semanticBFreq_sq (by positivity)]
  ring

theorem hasDerivAt_semanticMode {x a y m offset : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticMode x a z m offset)
      (semanticModePrime x a y m offset) y := by
  have hB := hasDerivAt_semanticBFreq (x := x) (a := a) hxa hy
  have hlinear := (hB.const_mul m).const_add offset
  have hsquare := hlinear.pow 2
  have hexponent := hsquare.const_mul (-(1 / 2 : ℝ))
  have hexp := hexponent.exp
  have hmodeRaw : HasDerivAt (fun z ↦ semanticMode x a z m offset)
      (Real.exp (-(1 / 2) * (offset + m * semanticBFreq x a y) ^ 2) *
        (-(1 / 2) * (2 * (offset + m * semanticBFreq x a y) *
          (m * (semanticBFreq x a y / (2 * y)))))) y := by
    simpa only [semanticMode, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using hexp
  apply hmodeRaw.congr_deriv
  dsimp [semanticModePrime, semanticMode]
  field_simp [hy.ne']
  ring

theorem hasDerivAt_semanticModePrime {x a y m offset : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticModePrime x a z m offset)
      (semanticModeSecond x a y m offset) y := by
  have hB := hasDerivAt_semanticBFreq (x := x) (a := a) hxa hy
  have hmode := hasDerivAt_semanticMode (x := x) (a := a)
    (m := m) (offset := offset) hxa hy
  have hyne : y ≠ 0 := hy.ne'
  have hnum : HasDerivAt
      (fun z ↦ -(m * semanticBFreq x a z *
        (m * semanticBFreq x a z + offset)))
      (-(m * (semanticBFreq x a y / (2 * y)) *
          (m * semanticBFreq x a y + offset) +
        m * semanticBFreq x a y *
          (m * (semanticBFreq x a y / (2 * y))))) y := by
    have hraw := ((hB.const_mul m).mul ((hB.const_mul m).const_add offset)).neg
    have hraw' : HasDerivAt
        (fun z ↦ -(m * semanticBFreq x a z *
          (m * semanticBFreq x a z + offset)))
        (-(m * (semanticBFreq x a y / (2 * y)) *
            (offset + m * semanticBFreq x a y) +
          m * semanticBFreq x a y *
            (m * (semanticBFreq x a y / (2 * y))))) y :=
      hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun z ↦ by
          simp only [Pi.neg_apply, Pi.mul_apply]
          ring))
    apply hraw'.congr_deriv
    ring
  have hden : HasDerivAt (fun z : ℝ ↦ 2 * z) 2 y :=
    hasDerivAt_const_mul 2
  have hfactor := hnum.div hden (by positivity : 2 * y ≠ 0)
  have hproduct := hmode.mul hfactor
  have hproduct' : HasDerivAt (fun z ↦ semanticModePrime x a z m offset)
      (semanticModePrime x a y m offset *
          (-(m * semanticBFreq x a y *
            (m * semanticBFreq x a y + offset)) / (2 * y)) +
        semanticMode x a y m offset *
          ((-(m * (semanticBFreq x a y / (2 * y)) *
                    (m * semanticBFreq x a y + offset) +
                  m * semanticBFreq x a y *
                    (m * (semanticBFreq x a y / (2 * y)))) * (2 * y) -
              -(m * semanticBFreq x a y *
                (m * semanticBFreq x a y + offset)) * 2) /
            (2 * y) ^ 2)) y := by
    have hcongr := hproduct.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        dsimp [semanticModePrime]))
    simpa only [semanticModePrime, Pi.mul_apply, Pi.div_apply] using hcongr
  apply hproduct'.congr_deriv
  dsimp [semanticModePrime, semanticModeSecond]
  field_simp [hyne]
  ring

/-- First Holder-weight derivative of the exact quadratic cosine moment. -/
noncomputable def semanticMomentTwoPrime (x a y : ℝ) : ℝ :=
  (1 / 4) *
    (semanticModePrime x a y 2 0 +
      (1 / 2) *
        (semanticModePrime x a y 2 (2 * semanticAFreq a) +
          semanticModePrime x a y 2 (-2 * semanticAFreq a)))

/-- Second Holder-weight derivative of the exact quadratic cosine moment. -/
noncomputable def semanticMomentTwoSecond (x a y : ℝ) : ℝ :=
  (1 / 4) *
    (semanticModeSecond x a y 2 0 +
      (1 / 2) *
        (semanticModeSecond x a y 2 (2 * semanticAFreq a) +
          semanticModeSecond x a y 2 (-2 * semanticAFreq a)))

/-- First derivative of one mixed moment in `semanticMomentFour`. -/
noncomputable def semanticMixedMomentPrime (x a y m : ℝ) : ℝ :=
  (1 / 2) * semanticModePrime x a y m 0 +
    (1 / 4) *
      (semanticModePrime x a y m (2 * semanticAFreq a) +
        semanticModePrime x a y m (-2 * semanticAFreq a))

/-- Second derivative of one mixed moment in `semanticMomentFour`. -/
noncomputable def semanticMixedMomentSecond (x a y m : ℝ) : ℝ :=
  (1 / 2) * semanticModeSecond x a y m 0 +
    (1 / 4) *
      (semanticModeSecond x a y m (2 * semanticAFreq a) +
        semanticModeSecond x a y m (-2 * semanticAFreq a))

/-- First Holder-weight derivative of the exact fourth cosine moment. -/
noncomputable def semanticMomentFourPrime (x a y : ℝ) : ℝ :=
  (1 / 2) * semanticMixedMomentPrime x a y 2 +
    (1 / 8) * semanticMixedMomentPrime x a y 4

/-- Second Holder-weight derivative of the exact fourth cosine moment. -/
noncomputable def semanticMomentFourSecond (x a y : ℝ) : ℝ :=
  (1 / 2) * semanticMixedMomentSecond x a y 2 +
    (1 / 8) * semanticMixedMomentSecond x a y 4

theorem semanticMomentTwo_eq_modes (x a y : ℝ) :
    semanticMomentTwo x a y =
      (1 / 4) *
        (1 + Real.exp (-2 * semanticAFreq a ^ 2) +
          semanticMode x a y 2 0 +
          (1 / 2) *
            (semanticMode x a y 2 (2 * semanticAFreq a) +
              semanticMode x a y 2 (-2 * semanticAFreq a))) := by
  dsimp [semanticMomentTwo, semanticMode]
  ring_nf

theorem semanticMixedMoment_eq_modes (x a y m : ℝ) :
    semanticMixedMoment x a y m =
      (1 / 2) * semanticMode x a y m 0 +
        (1 / 4) *
          (semanticMode x a y m (2 * semanticAFreq a) +
            semanticMode x a y m (-2 * semanticAFreq a)) := by
  dsimp [semanticMixedMoment, semanticMode]
  ring_nf

theorem hasDerivAt_semanticMomentTwo {x a y : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticMomentTwo x a z)
      (semanticMomentTwoPrime x a y) y := by
  have h0 := hasDerivAt_semanticMode (x := x) (a := a)
    (m := 2) (offset := 0) hxa hy
  have hp := hasDerivAt_semanticMode (x := x) (a := a)
    (m := 2) (offset := 2 * semanticAFreq a) hxa hy
  have hm := hasDerivAt_semanticMode (x := x) (a := a)
    (m := 2) (offset := -2 * semanticAFreq a) hxa hy
  have hraw := ((hasDerivAt_const y
      (1 + Real.exp (-2 * semanticAFreq a ^ 2))).add
      (h0.add ((hp.add hm).const_mul (1 / 2)))).const_mul (1 / 4)
  have hraw' : HasDerivAt (fun z ↦ semanticMomentTwo x a z)
      ((1 / 4) *
        (0 + (semanticModePrime x a y 2 0 +
          (1 / 2) *
            (semanticModePrime x a y 2 (2 * semanticAFreq a) +
              semanticModePrime x a y 2 (-2 * semanticAFreq a))))) y :=
    hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        change semanticMomentTwo x a z = _
        rw [semanticMomentTwo_eq_modes]
        simp only [Pi.add_apply]
        ring))
  exact hraw'.congr_deriv (by dsimp [semanticMomentTwoPrime]; ring)

theorem hasDerivAt_semanticMomentTwoPrime {x a y : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticMomentTwoPrime x a z)
      (semanticMomentTwoSecond x a y) y := by
  have h0 := hasDerivAt_semanticModePrime (x := x) (a := a)
    (m := 2) (offset := 0) hxa hy
  have hp := hasDerivAt_semanticModePrime (x := x) (a := a)
    (m := 2) (offset := 2 * semanticAFreq a) hxa hy
  have hm := hasDerivAt_semanticModePrime (x := x) (a := a)
    (m := 2) (offset := -2 * semanticAFreq a) hxa hy
  have hraw := (h0.add ((hp.add hm).const_mul (1 / 2))).const_mul (1 / 4)
  have hraw' : HasDerivAt (fun z ↦ semanticMomentTwoPrime x a z)
      ((1 / 4) *
        (semanticModeSecond x a y 2 0 +
          (1 / 2) *
            (semanticModeSecond x a y 2 (2 * semanticAFreq a) +
              semanticModeSecond x a y 2 (-2 * semanticAFreq a)))) y :=
    hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        dsimp [semanticMomentTwoPrime]))
  exact hraw'.congr_deriv (by rfl)

theorem hasDerivAt_semanticMixedMoment {x a y m : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticMixedMoment x a z m)
      (semanticMixedMomentPrime x a y m) y := by
  have h0 := hasDerivAt_semanticMode (x := x) (a := a)
    (m := m) (offset := 0) hxa hy
  have hp := hasDerivAt_semanticMode (x := x) (a := a)
    (m := m) (offset := 2 * semanticAFreq a) hxa hy
  have hm := hasDerivAt_semanticMode (x := x) (a := a)
    (m := m) (offset := -2 * semanticAFreq a) hxa hy
  have hraw := h0.const_mul (1 / 2) |>.add ((hp.add hm).const_mul (1 / 4))
  have hraw' : HasDerivAt (fun z ↦ semanticMixedMoment x a z m)
      ((1 / 2) * semanticModePrime x a y m 0 +
        (1 / 4) *
          (semanticModePrime x a y m (2 * semanticAFreq a) +
            semanticModePrime x a y m (-2 * semanticAFreq a))) y :=
    hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        change semanticMixedMoment x a z m = _
        rw [semanticMixedMoment_eq_modes]
        simp only [Pi.add_apply]))
  exact hraw'.congr_deriv (by dsimp [semanticMixedMomentPrime])

theorem hasDerivAt_semanticMixedMomentPrime {x a y m : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticMixedMomentPrime x a z m)
      (semanticMixedMomentSecond x a y m) y := by
  have h0 := hasDerivAt_semanticModePrime (x := x) (a := a)
    (m := m) (offset := 0) hxa hy
  have hp := hasDerivAt_semanticModePrime (x := x) (a := a)
    (m := m) (offset := 2 * semanticAFreq a) hxa hy
  have hm := hasDerivAt_semanticModePrime (x := x) (a := a)
    (m := m) (offset := -2 * semanticAFreq a) hxa hy
  have hraw := (h0.const_mul (1 / 2)).add ((hp.add hm).const_mul (1 / 4))
  have hraw' : HasDerivAt (fun z ↦ semanticMixedMomentPrime x a z m)
      ((1 / 2) * semanticModeSecond x a y m 0 +
        (1 / 4) *
          (semanticModeSecond x a y m (2 * semanticAFreq a) +
            semanticModeSecond x a y m (-2 * semanticAFreq a))) y :=
    hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        dsimp [semanticMixedMomentPrime]))
  exact hraw'.congr_deriv (by rfl)

theorem hasDerivAt_semanticMomentFour {x a y : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticMomentFour x a z)
      (semanticMomentFourPrime x a y) y := by
  have h2 := hasDerivAt_semanticMixedMoment (x := x) (a := a)
    (m := 2) hxa hy
  have h4 := hasDerivAt_semanticMixedMoment (x := x) (a := a)
    (m := 4) hxa hy
  have hraw := (hasDerivAt_const y
      ((3 / 8) * ((1 / 2) * (1 + Real.exp (-2 * semanticAFreq a ^ 2))))).add
      ((h2.const_mul (1 / 2)).add (h4.const_mul (1 / 8)))
  have hraw' : HasDerivAt (fun z ↦ semanticMomentFour x a z)
      (0 + ((1 / 2) * semanticMixedMomentPrime x a y 2 +
        (1 / 8) * semanticMixedMomentPrime x a y 4)) y :=
    hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        dsimp [semanticMomentFour]
        ring))
  exact hraw'.congr_deriv (by dsimp [semanticMomentFourPrime]; ring)

theorem hasDerivAt_semanticMomentFourPrime {x a y : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticMomentFourPrime x a z)
      (semanticMomentFourSecond x a y) y := by
  have h2 := hasDerivAt_semanticMixedMomentPrime (x := x) (a := a)
    (m := 2) hxa hy
  have h4 := hasDerivAt_semanticMixedMomentPrime (x := x) (a := a)
    (m := 4) hxa hy
  have hraw := (h2.const_mul (1 / 2)).add (h4.const_mul (1 / 8))
  have hraw' : HasDerivAt (fun z ↦ semanticMomentFourPrime x a z)
      ((1 / 2) * semanticMixedMomentSecond x a y 2 +
        (1 / 8) * semanticMixedMomentSecond x a y 4) y :=
    hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        dsimp [semanticMomentFourPrime]))
  exact hraw'.congr_deriv (by rfl)

noncomputable def semanticChordCentralPrime (x a y : ℝ) : ℝ :=
  (2 - 1 / y) * semanticMomentTwoPrime x a y +
    (1 / y - 1) * semanticMomentFourPrime x a y +
    (semanticMomentTwo x a y - semanticMomentFour x a y) / y ^ 2

/-- Exact second Holder-weight derivative used by the semiconvex cover. -/
noncomputable def semanticChordCentralSecond (x a y : ℝ) : ℝ :=
  (2 - 1 / y) * semanticMomentTwoSecond x a y +
    (1 / y - 1) * semanticMomentFourSecond x a y +
    2 / y ^ 2 *
      (semanticMomentTwoPrime x a y - semanticMomentFourPrime x a y) -
    2 / y ^ 3 * (semanticMomentTwo x a y - semanticMomentFour x a y)

theorem hasDerivAt_semanticChordCentral {x a y : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticChordCentral x a z)
      (semanticChordCentralPrime x a y) y := by
  have hyne : y ≠ 0 := hy.ne'
  have h2 := hasDerivAt_semanticMomentTwo (x := x) (a := a) hxa hy
  have h4 := hasDerivAt_semanticMomentFour (x := x) (a := a) hxa hy
  have hinv := (hasDerivAt_id y).inv hyne
  have hc2 := (hasDerivAt_const y 2).sub hinv
  have hc4 := hinv.sub_const 1
  have hraw := (hc2.mul h2).add (hc4.mul h4)
  have hrawNorm : HasDerivAt _
      ((1 / y ^ 2) * semanticMomentTwo x a y +
          (2 - 1 / y) * semanticMomentTwoPrime x a y +
        (-(1 / y ^ 2)) * semanticMomentFour x a y +
          (1 / y - 1) * semanticMomentFourPrime x a y) y :=
    hraw.congr_deriv (by
      simp only [id_eq, Pi.sub_apply, Pi.inv_apply, one_div]
      field_simp [hyne]
      ring)
  have hraw' : HasDerivAt (fun z ↦ semanticChordCentral x a z)
      ((1 / y ^ 2) * semanticMomentTwo x a y +
          (2 - 1 / y) * semanticMomentTwoPrime x a y +
        (-(1 / y ^ 2)) * semanticMomentFour x a y +
          (1 / y - 1) * semanticMomentFourPrime x a y) y :=
    hrawNorm.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        dsimp [semanticChordCentral]
        simp only [one_div]))
  apply hraw'.congr_deriv
  dsimp [semanticChordCentralPrime]
  field_simp [hyne]
  ring

theorem hasDerivAt_semanticChordCentralPrime {x a y : ℝ}
    (hxa : 0 < x - a) (hy : 0 < y) :
    HasDerivAt (fun z ↦ semanticChordCentralPrime x a z)
      (semanticChordCentralSecond x a y) y := by
  have hyne : y ≠ 0 := hy.ne'
  have h2 := hasDerivAt_semanticMomentTwo (x := x) (a := a) hxa hy
  have h2p := hasDerivAt_semanticMomentTwoPrime (x := x) (a := a) hxa hy
  have h4 := hasDerivAt_semanticMomentFour (x := x) (a := a) hxa hy
  have h4p := hasDerivAt_semanticMomentFourPrime (x := x) (a := a) hxa hy
  have hinv := (hasDerivAt_id y).inv hyne
  have hc2 := (hasDerivAt_const y 2).sub hinv
  have hc4 := hinv.sub_const 1
  have hdiff := h2.sub h4
  have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
    have hrawSq := (hasDerivAt_id y).pow 2
    have hrawSq' : HasDerivAt (fun z : ℝ ↦ z ^ 2)
        (2 * y ^ (2 - 1) * 1) y :=
      hrawSq.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun z ↦ by rfl))
    exact hrawSq'.congr_deriv (by norm_num)
  have hquot := hdiff.div hsq (by positivity : y ^ 2 ≠ 0)
  have hraw := ((hc2.mul h2p).add (hc4.mul h4p)).add hquot
  have hrawNorm : HasDerivAt _
      ((1 / y ^ 2) * semanticMomentTwoPrime x a y +
          (2 - 1 / y) * semanticMomentTwoSecond x a y +
        (-(1 / y ^ 2)) * semanticMomentFourPrime x a y +
          (1 / y - 1) * semanticMomentFourSecond x a y +
        ((semanticMomentTwoPrime x a y - semanticMomentFourPrime x a y) * y ^ 2 -
          (semanticMomentTwo x a y - semanticMomentFour x a y) * (2 * y)) /
            (y ^ 2) ^ 2) y :=
    hraw.congr_deriv (by
      simp only [id_eq, Pi.sub_apply, Pi.inv_apply, one_div]
      field_simp [hyne]
      ring)
  have hraw' : HasDerivAt (fun z ↦ semanticChordCentralPrime x a z)
      ((1 / y ^ 2) * semanticMomentTwoPrime x a y +
          (2 - 1 / y) * semanticMomentTwoSecond x a y +
        (-(1 / y ^ 2)) * semanticMomentFourPrime x a y +
          (1 / y - 1) * semanticMomentFourSecond x a y +
        ((semanticMomentTwoPrime x a y - semanticMomentFourPrime x a y) * y ^ 2 -
          (semanticMomentTwo x a y - semanticMomentFour x a y) * (2 * y)) /
            (y ^ 2) ^ 2) y :=
    hrawNorm.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z ↦ by
        dsimp [semanticChordCentralPrime]
        simp only [one_div]))
  apply hraw'.congr_deriv
  dsimp [semanticChordCentralSecond]
  field_simp [hyne]
  ring

end ThresholdNearChord128
end CertifiedJL
