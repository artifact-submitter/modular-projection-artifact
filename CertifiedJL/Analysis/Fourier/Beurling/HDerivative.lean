/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author

The termwise-differentiation argument is adapted from
`MathExtras/NumberTheory/Analysis/VaalerDerivInterpHProbe.lean` in
`gersh/ternary-goldbach-lean`, commit
`89416190c037331d7ebc04cd62ddb974cfb4dfcf` (Apache-2.0),
copyright (c) 2026 Gershon Bialer.
-/

import CertifiedJL.Analysis.Fourier.Beurling.Majorant
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiating the Beurling interpolant

This file proves the elementary half of the Fourier identity for Beurling's
odd interpolant.  On the positive half-line, our definition of `beurlingH`
uses only the pole-free reciprocal-square tail

`∑' n, (x + (n + 1))⁻²`.

We differentiate that tail term by term on a ball contained in `(0, ∞)`,
then apply the ordinary product rule to the explicit formula for
`beurlingH`.  The resulting derivative is completely explicit.  Identifying
that expression with `2 * re (beurlingJ x)` is the separate Fourier-analytic
step in Vaaler's theorem.
-/

open Filter MeasureTheory Real Topology
open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- Derivative of a translated reciprocal square away from its pole. -/
theorem hasDerivAt_invSq_sub (c x : ℝ) (hx : x - c ≠ 0) :
    HasDerivAt (fun y : ℝ => (y - c)⁻¹ ^ 2)
      (-2 * (x - c)⁻¹ ^ 3) x := by
  have hinner : HasDerivAt (fun y : ℝ => y - c) 1 x := by
    simpa using (hasDerivAt_id x).sub_const c
  have hinv := hinner.inv hx
  refine (hinv.pow 2).congr_deriv ?_
  simp only [Pi.inv_apply]
  field_simp [hx]
  have hcancel : (x - c) * (x - c)⁻¹ = 1 := mul_inv_cancel₀ hx
  calc
    _ = -2 * ((x - c) * (x - c)⁻¹) := by ring
    _ = -2 := by rw [hcancel]; ring

/-- Derivative of one summand in `beurlingReciprocalSquareTail`. -/
theorem hasDerivAt_beurlingTailTerm (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => (y + (n + 1 : ℕ))⁻¹ ^ 2)
      (-2 * (x + (n + 1 : ℕ))⁻¹ ^ 3) x := by
  have hne : x - (-(n + 1 : ℕ) : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < x + ((n : ℝ) + 1) := by positivity
    push_cast
    intro h
    nlinarith
  have h :=
    hasDerivAt_invSq_sub (-(n + 1 : ℕ) : ℝ) x hne
  have hfun :
      (fun y : ℝ => (y - (-(n + 1 : ℕ) : ℝ))⁻¹ ^ 2) =
        fun y : ℝ => (y + (n + 1 : ℕ))⁻¹ ^ 2 := by
    funext y
    push_cast
    congr 2
    ring
  rw [hfun] at h
  convert h using 1
  push_cast
  ring

/-- The cubic derivative series is summable on the positive half-line. -/
theorem summable_beurlingTailDerivative {x : ℝ} (hx : 0 < x) :
    Summable
      (fun n : ℕ => -2 * (x + (n + 1 : ℕ))⁻¹ ^ 3) := by
  apply Summable.mul_left
  have hsq :
      Summable
        (fun n : ℕ => (x + (n + 1 : ℕ))⁻¹ ^ 2) := by
    simpa [one_div, inv_pow] using
      summable_beurlingReciprocalSquareTail hx
  refine Summable.of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_) hsq
  have hbase : (1 : ℝ) ≤ x + (n + 1 : ℕ) := by
    push_cast
    nlinarith [hx.le, Nat.cast_nonneg (α := ℝ) n]
  have hinv : (x + (n + 1 : ℕ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hbase
  calc
    (x + (n + 1 : ℕ))⁻¹ ^ 3 =
        (x + (n + 1 : ℕ))⁻¹ ^ 2 *
          (x + (n + 1 : ℕ))⁻¹ := by ring
    _ ≤ (x + (n + 1 : ℕ))⁻¹ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (x + (n + 1 : ℕ))⁻¹ ^ 2 := by ring

/--
Uniform summable domination for the derivative series on the ball
`ball x (x / 2)`, which lies inside the positive half-line.
-/
theorem beurlingTailDerivative_localBound {x : ℝ} (hx : 0 < x) :
    Summable
        (fun n : ℕ =>
          2 * (x / 2 + (n + 1 : ℕ))⁻¹ ^ 3) ∧
      ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball x (x / 2) →
        ‖-2 * (y + (n + 1 : ℕ))⁻¹ ^ 3‖ ≤
          2 * (x / 2 + (n + 1 : ℕ))⁻¹ ^ 3 := by
  have hhalf : 0 < x / 2 := by positivity
  constructor
  · have h := (summable_beurlingTailDerivative hhalf).neg
    refine h.congr ?_
    intro n
    ring
  · intro n y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hylower : x / 2 < y := by
      rcases abs_lt.mp hy with ⟨hleft, _⟩
      linarith
    have hbase : 0 < x / 2 + (n + 1 : ℕ) := by positivity
    have hbase' : 0 < y + (n + 1 : ℕ) := by
      have hn : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
      linarith
    have hle :
        x / 2 + (n + 1 : ℕ) ≤ y + (n + 1 : ℕ) := by
      linarith
    have hinv :
        (y + (n + 1 : ℕ))⁻¹ ≤
          (x / 2 + (n + 1 : ℕ))⁻¹ :=
      inv_anti₀ hbase hle
    have hpow :
        (y + (n + 1 : ℕ))⁻¹ ^ 3 ≤
          (x / 2 + (n + 1 : ℕ))⁻¹ ^ 3 :=
      pow_le_pow_left₀ (by positivity) hinv 3
    have hnonneg :
        0 ≤ (y + (n + 1 : ℕ))⁻¹ ^ 3 := by positivity
    rw [Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith [hnonneg]), neg_mul]
    linarith

set_option maxHeartbeats 1000000 in
-- The smooth-series theorem elaborates a locally uniform bound through a
-- dependent family of derivative witnesses.
/--
The reciprocal-square tail may be differentiated term by term at every
positive point.
-/
theorem hasDerivAt_beurlingReciprocalSquareTail
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt beurlingReciprocalSquareTail
      (∑' n : ℕ, -2 * (x + (n + 1 : ℕ))⁻¹ ^ 3) x := by
  obtain ⟨hboundSummable, hbound⟩ :=
    beurlingTailDerivative_localBound hx
  have hhalf : 0 < x / 2 := by positivity
  let s : Set ℝ := Metric.ball x (x / 2)
  have hopen : IsOpen s := Metric.isOpen_ball
  have hconnected : IsPreconnected s :=
    (convex_ball x (x / 2)).isPreconnected
  have hxmem : x ∈ s := Metric.mem_ball_self hhalf
  have hterm :
      ∀ (n : ℕ) (y : ℝ), y ∈ s →
        HasDerivAt
          (fun z : ℝ => (z + (n + 1 : ℕ))⁻¹ ^ 2)
          (-2 * (y + (n + 1 : ℕ))⁻¹ ^ 3) y := by
    intro n y hy
    change y ∈ Metric.ball x (x / 2) at hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hypos : 0 < y := by
      rcases abs_lt.mp hy with ⟨hleft, _⟩
      linarith
    exact hasDerivAt_beurlingTailTerm n hypos
  have hvalue :
      Summable
        (fun n : ℕ => (x + (n + 1 : ℕ))⁻¹ ^ 2) := by
    simpa [one_div, inv_pow] using
      summable_beurlingReciprocalSquareTail hx
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ =>
      2 * (x / 2 + (n + 1 : ℕ))⁻¹ ^ 3)
    (g := fun (n : ℕ) (z : ℝ) =>
      (z + (n + 1 : ℕ))⁻¹ ^ 2)
    (g' := fun (n : ℕ) (y : ℝ) =>
      -2 * (y + (n + 1 : ℕ))⁻¹ ^ 3)
    hboundSummable hopen hconnected hterm hbound hxmem
    hvalue hxmem
  have hfun :
      beurlingReciprocalSquareTail =
        fun z : ℝ =>
          ∑' n : ℕ, (z + (n + 1 : ℕ))⁻¹ ^ 2 := by
    funext z
    simp only [beurlingReciprocalSquareTail, one_div, inv_pow]
  rw [hfun]
  exact hmain

/-- The explicit positive-half-line derivative of `beurlingH`. -/
noncomputable def beurlingHPositiveDerivative (x : ℝ) : ℝ :=
  let sineFactor := Real.sin (Real.pi * x) / Real.pi
  let bracket :=
    2 / x - 1 / x ^ 2 -
      2 * beurlingReciprocalSquareTail x
  let bracketDerivative :=
    -2 / x ^ 2 + 2 / x ^ 3 -
      2 * (∑' n : ℕ,
        -2 * (x + (n + 1 : ℕ))⁻¹ ^ 3)
  2 * sineFactor * Real.cos (Real.pi * x) * bracket +
    sineFactor ^ 2 * bracketDerivative

/--
Closed-form derivative of `beurlingH` on the positive half-line.

This is the elementary termwise-differentiation statement.  Vaaler's
Fourier theorem supplies the further identity
`beurlingHPositiveDerivative x = 2 * (beurlingJ x).re`.
-/
theorem hasDerivAt_beurlingH_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt beurlingH (beurlingHPositiveDerivative x) x := by
  have hxne : x ≠ 0 := hx.ne'
  have htail :=
    hasDerivAt_beurlingReciprocalSquareTail hx
  have hsinInner :
      HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    simpa using (hasDerivAt_id x).const_mul Real.pi
  have hsin :
      HasDerivAt
        (fun y : ℝ => Real.sin (Real.pi * y) / Real.pi)
        (Real.cos (Real.pi * x)) x := by
    simpa [Real.pi_ne_zero] using
      (((Real.hasDerivAt_sin (Real.pi * x)).comp x hsinInner).div_const
        Real.pi)
  have htwoDiv :
      HasDerivAt (fun y : ℝ => 2 / y) (-2 / x ^ 2) x := by
    simpa [div_eq_mul_inv, inv_pow] using
      (hasDerivAt_inv hxne).const_mul (2 : ℝ)
  have honeDivSq :
      HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x := by
    simpa [div_eq_mul_inv, inv_pow] using
      hasDerivAt_invSq_sub 0 x (by simpa using hxne)
  have hbracket :
      HasDerivAt
        (fun y : ℝ =>
          2 / y - 1 / y ^ 2 -
            2 * beurlingReciprocalSquareTail y)
        (-2 / x ^ 2 + 2 / x ^ 3 -
          2 * (∑' n : ℕ,
            -2 * (x + (n + 1 : ℕ))⁻¹ ^ 3)) x := by
    have hraw :
        HasDerivAt
          (fun y : ℝ =>
            2 / y - 1 / y ^ 2 -
              2 * beurlingReciprocalSquareTail y)
          ((-2 / x ^ 2) - (-2 / x ^ 3) -
            2 * (∑' n : ℕ,
              -2 * (x + (n + 1 : ℕ))⁻¹ ^ 3)) x := by
      exact (htwoDiv.sub honeDivSq).sub (htail.const_mul 2)
    exact hraw.congr_deriv (by ring)
  have hproduct :=
    (hsin.pow 2).mul hbracket
  have hformula :
      HasDerivAt
        (fun y : ℝ =>
          1 + (Real.sin (Real.pi * y) / Real.pi) ^ 2 *
            (2 / y - 1 / y ^ 2 -
              2 * beurlingReciprocalSquareTail y))
        (beurlingHPositiveDerivative x) x := by
    refine (hproduct.const_add 1).congr_deriv ?_
    simp only [beurlingHPositiveDerivative]
    dsimp
    ring
  have heventually :
      beurlingH =ᶠ[nhds x]
        fun y : ℝ =>
          1 + (Real.sin (Real.pi * y) / Real.pi) ^ 2 *
            (2 / y - 1 / y ^ 2 -
              2 * beurlingReciprocalSquareTail y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [beurlingH_of_pos hy]
  exact hformula.congr_of_eventuallyEq heventually

end Probability
end CertifiedJL
