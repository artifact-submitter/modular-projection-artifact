/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Quadrature.EndpointRiemann
import CertifiedJL.Arithmetic.Quadrature.Trapezoid
import CertifiedJL.Probability.NormalApproximation.Tyurin.GlobalEnvelope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Closed bounds for Tyurin's discrepancy envelopes

The Prawitz certificate must bound integrals whose integrands contain
`tyurinDeltaOne` and `tyurinDeltaTwo`.  Directly nesting numerical quadrature
would make the checker both expensive and difficult to audit.  This file
eliminates the inner integrals with elementary monotone bounds.

The statements here deliberately remain independent of any grid or numerical
precision.  A later certificate may therefore choose its partition without
changing the analytic proof.
-/

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

/-- A finite right-endpoint sum for the quadratic-exponential integral. -/
noncomputable def sqExpSqRightSum
    (n : ℕ) (c T : ℝ) : ℝ :=
  (T / n) *
    ∑ i ∈ Finset.range n,
      let s := (T / n) * (i + 1 : ℕ)
      s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)

/-- A finite right-endpoint sum for a cubic exponential on `[A,T]`. -/
noncomputable def sqExpCubeRightSum
    (n : ℕ) (c A T : ℝ) : ℝ :=
  ((T - A) / n) *
    ∑ i ∈ Finset.range n,
      let s := A + ((T - A) / n) * (i + 1 : ℕ)
      s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5)

/-- A finite trapezoidal upper sum for the quadratic-exponential integral. -/
noncomputable def sqExpSqTrapezoid
    (n : ℕ) (c T : ℝ) : ℝ :=
  trapezoidal_integral
    (fun s : ℝ =>
      s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2))
    n 0 T

/-- A finite trapezoidal upper sum for a cubic exponential on `[A,T]`. -/
noncomputable def sqExpCubeTrapezoid
    (n : ℕ) (c A T : ℝ) : ℝ :=
  trapezoidal_integral
    (fun s : ℝ =>
      s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5))
    n A T

theorem monotoneOn_sq_div_two_mul_exp_sq
    {c : ℝ} (hc : 0 ≤ c) :
    MonotoneOn
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2))
      (Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hsq : x ^ 2 ≤ y ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hx0 hxy
  have hExp :
      Real.exp (c * x ^ 2 / 2) ≤
        Real.exp (c * y ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul (by nlinarith : x ^ 2 / 2 ≤ y ^ 2 / 2)
    hExp (Real.exp_nonneg _) (by positivity)

theorem monotoneOn_sq_div_two_mul_exp_cube
    {c : ℝ} (hc : 0 ≤ c) :
    MonotoneOn
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5))
      (Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hsq : x ^ 2 ≤ y ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hx0 hxy
  have hcube : x ^ 3 ≤ y ^ 3 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ ≤ y * y ^ 2 :=
        mul_le_mul hxy hsq (sq_nonneg x) hy0
      _ = y ^ 3 := by ring
  have hExp :
      Real.exp (c * x ^ 3 / 5) ≤
        Real.exp (c * y ^ 3 / 5) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul (by nlinarith : x ^ 2 / 2 ≤ y ^ 2 / 2)
    hExp (Real.exp_nonneg _) (by positivity)

theorem convexOn_sq_div_two_mul_exp_sq
    {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ (Ici 0)
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)) := by
  let f : ℝ → ℝ := fun s =>
    s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)
  let f' : ℝ → ℝ := fun s =>
    s * Real.exp (c * s ^ 2 / 2) *
      (1 + c * s ^ 2 / 2)
  let f'' : ℝ → ℝ := fun s =>
    Real.exp (c * s ^ 2 / 2) *
      (1 + 5 * c * s ^ 2 / 2 + c ^ 2 * s ^ 4 / 2)
  have hinner (s : ℝ) :
      HasDerivAt (fun x : ℝ => c * x ^ 2 / 2) (c * s) s := by
    convert ((hasDerivAt_pow 2 s).const_mul c).div_const 2 using 1 <;>
      first | rfl | ring
  have hf' (s : ℝ) : HasDerivAt f (f' s) s := by
    dsimp [f, f']
    convert ((hasDerivAt_pow 2 s).div_const 2).mul
      (hinner s).exp using 1 <;>
      first | rfl | ring
  have hf'' (s : ℝ) : HasDerivAt f' (f'' s) s := by
    dsimp [f', f'']
    have hone :
        HasDerivAt (fun x : ℝ => 1 + c * x ^ 2 / 2)
          (c * s) s := by
      convert (hasDerivAt_const (x := s) (c := (1 : ℝ))).add
        (hinner s) using 1 <;>
        first | rfl | ring
    convert
      ((hasDerivAt_id s).mul (hinner s).exp).mul hone using 1 <;>
      first | rfl | (simp only [id_eq, Pi.mul_apply]; ring)
  change ConvexOn ℝ (Ici 0) f
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Ici (0 : ℝ))
    (by
      intro s _
      exact (hf' s).continuousAt.continuousWithinAt)
    (fun s _ => (hf' s).hasDerivWithinAt)
    (fun s _ => (hf'' s).hasDerivWithinAt)
  intro s hs
  dsimp [f'']
  have hs0 : 0 ≤ s := interior_subset hs
  positivity

theorem convexOn_sq_div_two_mul_exp_cube
    {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ (Ici 0)
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5)) := by
  let f : ℝ → ℝ := fun s =>
    s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5)
  let f' : ℝ → ℝ := fun s =>
    Real.exp (c * s ^ 3 / 5) *
      (s + 3 * c * s ^ 4 / 10)
  let f'' : ℝ → ℝ := fun s =>
    Real.exp (c * s ^ 3 / 5) *
      (1 + 9 * c * s ^ 3 / 5 +
        9 * c ^ 2 * s ^ 6 / 50)
  have hinner (s : ℝ) :
      HasDerivAt (fun x : ℝ => c * x ^ 3 / 5)
        (3 * c * s ^ 2 / 5) s := by
    convert ((hasDerivAt_pow 3 s).const_mul c).div_const 5 using 1 <;>
      first | rfl | ring
  have hf' (s : ℝ) : HasDerivAt f (f' s) s := by
    dsimp [f, f']
    convert ((hasDerivAt_pow 2 s).div_const 2).mul
      (hinner s).exp using 1 <;>
      first | rfl | ring
  have hf'' (s : ℝ) : HasDerivAt f' (f'' s) s := by
    dsimp [f', f'']
    have hpoly :
        HasDerivAt
          (fun x : ℝ => x + 3 * c * x ^ 4 / 10)
          (1 + 6 * c * s ^ 3 / 5) s := by
      convert (hasDerivAt_id s).add
        (((hasDerivAt_pow 4 s).const_mul (3 * c)).div_const 10)
        using 1 <;>
        first | rfl | ring
    convert (hinner s).exp.mul hpoly using 1 <;>
      first | rfl | ring
  change ConvexOn ℝ (Ici 0) f
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Ici (0 : ℝ))
    (by
      intro s _
      exact (hf' s).continuousAt.continuousWithinAt)
    (fun s _ => (hf' s).hasDerivWithinAt)
    (fun s _ => (hf'' s).hasDerivWithinAt)
  intro s hs
  dsimp [f'']
  have hs0 : 0 ≤ s := interior_subset hs
  positivity

/--
Soundness of the finite quadratic-exponential right sum.
-/
theorem integral_sq_div_two_mul_exp_sq_le_rightSum
    {n : ℕ} {T c : ℝ} (hn : 0 < n)
    (hT : 0 ≤ T) (hc : 0 ≤ c) :
    (∫ s : ℝ in 0..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)) ≤
      sqExpSqRightSum n c T := by
  unfold sqExpSqRightSum
  apply intervalIntegral_le_rightRiemannSum n hT hn
  exact (monotoneOn_sq_div_two_mul_exp_sq hc).mono Icc_subset_Ici_self

/--
Soundness of the finite cubic-exponential right sum.
-/
theorem integral_sq_div_two_mul_exp_cube_le_rightSum
    {n : ℕ} {A T c : ℝ} (hn : 0 < n)
    (hA : 0 ≤ A) (hAT : A ≤ T) (hc : 0 ≤ c) :
    (∫ s : ℝ in A..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5)) ≤
      sqExpCubeRightSum n c A T := by
  unfold sqExpCubeRightSum
  apply intervalIntegral_le_rightRiemannSum_of_le n hAT hn
  exact (monotoneOn_sq_div_two_mul_exp_cube hc).mono
    (by
      intro s hs
      exact hA.trans hs.1)

/--
Soundness of the finite quadratic-exponential trapezoidal upper sum.
-/
theorem integral_sq_div_two_mul_exp_sq_le_trapezoid
    {n : ℕ} {T c : ℝ} (hn : 0 < n)
    (hT : 0 ≤ T) (hc : 0 ≤ c) :
    (∫ s : ℝ in 0..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)) ≤
      sqExpSqTrapezoid n c T := by
  unfold sqExpSqTrapezoid
  apply intervalIntegral_le_trapezoidalIntegral_of_convexOn
    n hT hn
  · refine ⟨convex_Icc 0 T, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (convexOn_sq_div_two_mul_exp_sq hc).2
      (Icc_subset_Ici_self hx) (Icc_subset_Ici_self hy)
      ha hb hab
  · exact (by fun_prop : Continuous
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2))).continuousOn

/--
Soundness of the finite cubic-exponential trapezoidal upper sum.
-/
theorem integral_sq_div_two_mul_exp_cube_le_trapezoid
    {n : ℕ} {A T c : ℝ} (hn : 0 < n)
    (hA : 0 ≤ A) (hAT : A ≤ T) (hc : 0 ≤ c) :
    (∫ s : ℝ in A..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5)) ≤
      sqExpCubeTrapezoid n c A T := by
  unfold sqExpCubeTrapezoid
  apply intervalIntegral_le_trapezoidalIntegral_of_convexOn
    n hAT hn
  · refine ⟨convex_Icc A T, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (convexOn_sq_div_two_mul_exp_cube hc).2
      (hA.trans hx.1) (hA.trans hy.1) ha hb hab
  · exact (by fun_prop : Continuous
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5))).continuousOn

theorem sqExpSqTrapezoid_nonneg
    {n : ℕ} {c T : ℝ} (hn : 0 < n) (hT : 0 ≤ T) :
    0 ≤ sqExpSqTrapezoid n c T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold sqExpSqTrapezoid trapezoidal_integral
  simp only [sub_zero, zero_add]
  apply mul_nonneg (div_nonneg hT hnR.le)
  apply add_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro k _
    positivity

/--
The trapezoidal upper sum is no larger than interval length times the
right-endpoint value.  This coarse estimate is used only to prove that the
certificate integrand has a removable singularity at zero.
-/
theorem sqExpSqTrapezoid_le_endpoint
    {n : ℕ} {c T : ℝ} (hn : 0 < n) (hT : 0 ≤ T)
    (hc : 0 ≤ c) :
    sqExpSqTrapezoid n c T ≤
      T ^ 3 / 2 * Real.exp (c * T ^ 2 / 2) := by
  let f : ℝ → ℝ := fun s =>
    s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnode :
      ∀ k ∈ Finset.range (n - 1),
        f (((k : ℝ) + 1) * T / n) ≤ f T := by
    intro k hk
    have hkNat : k + 1 ≤ n :=
      (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)).trans
        (Nat.sub_le n 1)
    have hkR : ((k + 1 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hkNat
    have hs0 : 0 ≤ ((k : ℝ) + 1) * T / n := by
      positivity
    have hsT : ((k : ℝ) + 1) * T / n ≤ T := by
      rw [div_le_iff₀ hnR]
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using
        mul_le_mul_of_nonneg_right hkR hT
    exact monotoneOn_sq_div_two_mul_exp_sq hc hs0 hT hsT
  have hsum :
      ∑ k ∈ Finset.range (n - 1), f (((k : ℝ) + 1) * T / n) ≤
        (n - 1 : ℕ) * f T := by
    calc
      ∑ k ∈ Finset.range (n - 1), f (((k : ℝ) + 1) * T / n)
          ≤ ∑ _k ∈ Finset.range (n - 1), f T :=
        Finset.sum_le_sum fun k hk => hnode k hk
      _ = (n - 1 : ℕ) * f T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcount : ((n - 1 : ℕ) : ℝ) + 1 / 2 ≤ n := by
    have hnOne : 1 ≤ n := hn
    rw [Nat.cast_sub hnOne]
    linarith
  have hfT0 : 0 ≤ f T := by
    dsimp [f]
    positivity
  have hcalc :
    (T / n) *
        ((f 0 + f T) / 2 +
          ∑ k ∈ Finset.range (n - 1),
            f (((k : ℝ) + 1) * T / n)) ≤
      T ^ 3 / 2 * Real.exp (c * T ^ 2 / 2) := by
    rw [show f 0 = 0 by simp [f], zero_add]
    calc
      (T / n) *
          (f T / 2 +
            ∑ k ∈ Finset.range (n - 1),
              f (((k : ℝ) + 1) * T / n))
          ≤ (T / n) * (f T / 2 + (n - 1 : ℕ) * f T) := by
            gcongr
      _ ≤ (T / n) * ((n : ℝ) * f T) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc
              f T / 2 + (n - 1 : ℕ) * f T =
                  (((n - 1 : ℕ) : ℝ) + 1 / 2) * f T := by ring
              _ ≤ (n : ℝ) * f T :=
                mul_le_mul_of_nonneg_right hcount hfT0
      _ = T ^ 3 / 2 * Real.exp (c * T ^ 2 / 2) := by
            dsimp [f]
            field_simp [hnR.ne']
  simpa [sqExpSqTrapezoid, trapezoidal_integral, f] using hcalc

/--
The elementary endpoint bound for
`∫ s in 0..T, s² / 2 * exp (c * s² / 2)`.
-/
theorem integral_sq_div_two_mul_exp_sq_le
    {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c) :
    (∫ s : ℝ in 0..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)) ≤
      T ^ 3 / 6 * Real.exp (c * T ^ 2 / 2) := by
  have hf :
      IntervalIntegrable
        (fun s : ℝ => s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2))
        volume 0 T := by
    exact (by fun_prop : Continuous
      (fun s : ℝ => s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2))).intervalIntegrable _ _
  have hg :
      IntervalIntegrable
        (fun s : ℝ =>
          s ^ 2 / 2 * Real.exp (c * T ^ 2 / 2))
        volume 0 T := by
    exact (by fun_prop : Continuous
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * T ^ 2 / 2))).intervalIntegrable _ _
  calc
    (∫ s : ℝ in 0..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2))
        ≤ ∫ s : ℝ in 0..T,
            s ^ 2 / 2 * Real.exp (c * T ^ 2 / 2) := by
          apply intervalIntegral.integral_mono_on hT hf hg
          intro s hs
          have hs0 : 0 ≤ s := hs.1
          have hsT : s ≤ T := hs.2
          have hsSq : s ^ 2 ≤ T ^ 2 := by
            nlinarith
          have hExp :
              Real.exp (c * s ^ 2 / 2) ≤
                Real.exp (c * T ^ 2 / 2) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          exact mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = T ^ 3 / 6 * Real.exp (c * T ^ 2 / 2) := by
          rw [intervalIntegral.integral_mul_const,
            intervalIntegral.integral_div,
            integral_pow]
          ring

/--
The corresponding endpoint bound for a cubic exponential on a nonnegative
interval.
-/
theorem integral_sq_div_two_mul_exp_cube_le
    {A T c : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T) (hc : 0 ≤ c) :
    (∫ s : ℝ in A..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5)) ≤
      (T ^ 3 - A ^ 3) / 6 *
        Real.exp (c * T ^ 3 / 5) := by
  have hf :
      IntervalIntegrable
        (fun s : ℝ => s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5))
        volume A T := by
    exact (by fun_prop : Continuous
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5))).intervalIntegrable _ _
  have hg :
      IntervalIntegrable
        (fun s : ℝ =>
          s ^ 2 / 2 * Real.exp (c * T ^ 3 / 5))
        volume A T := by
    exact (by fun_prop : Continuous
      (fun s : ℝ =>
        s ^ 2 / 2 * Real.exp (c * T ^ 3 / 5))).intervalIntegrable _ _
  calc
    (∫ s : ℝ in A..T,
        s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5))
        ≤ ∫ s : ℝ in A..T,
            s ^ 2 / 2 * Real.exp (c * T ^ 3 / 5) := by
          apply intervalIntegral.integral_mono_on hAT hf hg
          intro s hs
          have hs0 : 0 ≤ s := hA.trans hs.1
          have hsT : s ≤ T := hs.2
          have hT0 : 0 ≤ T := hs0.trans hsT
          have hsSq : s ^ 2 ≤ T ^ 2 := by
            nlinarith
          have hsCube : s ^ 3 ≤ T ^ 3 := by
            calc
              s ^ 3 = s * s ^ 2 := by ring
              _ ≤ T * T ^ 2 := by nlinarith
              _ = T ^ 3 := by ring
          have hExp :
              Real.exp (c * s ^ 3 / 5) ≤
                Real.exp (c * T ^ 3 / 5) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          exact mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = (T ^ 3 - A ^ 3) / 6 *
          Real.exp (c * T ^ 3 / 5) := by
          rw [intervalIntegral.integral_mul_const,
            intervalIntegral.integral_div,
            integral_pow]
          ring

/--
The first Tyurin discrepancy is at most its cubic Taylor envelope.
-/
theorem tyurinDeltaOne_le_cubic
    {L t : ℝ} (hL : 0 ≤ L) :
    tyurinDeltaOne L t ≤ L * |t| ^ 3 / 6 := by
  have hT : 0 ≤ |t| := abs_nonneg _
  have hIntegral :=
    integral_sq_div_two_mul_exp_sq_le hT (show (0 : ℝ) ≤ 1 by norm_num)
  unfold tyurinDeltaOne
  rw [show (fun s : ℝ => s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) =
      (fun s : ℝ => s ^ 2 / 2 * Real.exp (1 * s ^ 2 / 2)) by
    funext s
    ring_nf]
  calc
    L * Real.exp (-(|t| ^ 2) / 2) *
        (∫ s : ℝ in 0..|t|,
          s ^ 2 / 2 * Real.exp (1 * s ^ 2 / 2)) ≤
        L * Real.exp (-(|t| ^ 2) / 2) *
          (|t| ^ 3 / 6 * Real.exp (1 * |t| ^ 2 / 2)) := by
          gcongr
    _ = L * |t| ^ 3 / 6 := by
          rw [show (1 : ℝ) * |t| ^ 2 / 2 = |t| ^ 2 / 2 by ring,
            show
              L * Real.exp (-(|t| ^ 2) / 2) *
                  (|t| ^ 3 / 6 * Real.exp (|t| ^ 2 / 2)) =
                L * |t| ^ 3 / 6 *
                  (Real.exp (-(|t| ^ 2) / 2) *
                    Real.exp (|t| ^ 2 / 2)) by ring,
            ← Real.exp_add]
          ring_nf
          rw [Real.exp_zero]
          ring

/--
On the first branch, `tyurinDeltaTwo` admits a closed endpoint bound.
The exponent is kept in factored form because this is the form consumed by
the interval certificate.
-/
theorem tyurinDeltaTwo_le_firstClosed
    {L t : ℝ} (hL : 0 ≤ L)
    (hbranch : |t| * lyapunovThirdRoot L ≤ 5 / 3) :
    tyurinDeltaTwo L t ≤
      L * |t| ^ 3 / 6 *
        Real.exp
          (-((1 - lyapunovVarianceCap L) * |t| ^ 2) / 2) := by
  let T : ℝ := |t|
  let c : ℝ := lyapunovVarianceCap L
  have hT : 0 ≤ T := abs_nonneg _
  have hc : 0 ≤ c := lyapunovVarianceCap_nonneg hL
  have hIntegral := integral_sq_div_two_mul_exp_sq_le hT hc
  have hExpNonneg : 0 ≤ Real.exp (-(T ^ 2) / 2) :=
    (Real.exp_pos _).le
  unfold tyurinDeltaTwo
  dsimp only
  rw [if_pos hbranch]
  change
    L * Real.exp (-(T ^ 2) / 2) *
        (∫ s : ℝ in 0..T,
          s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)) ≤
      L * T ^ 3 / 6 *
        Real.exp (-((1 - c) * T ^ 2) / 2)
  calc
    L * Real.exp (-(T ^ 2) / 2) *
        (∫ s : ℝ in 0..T,
          s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2))
        ≤ L * Real.exp (-(T ^ 2) / 2) *
            (T ^ 3 / 6 * Real.exp (c * T ^ 2 / 2)) := by
          gcongr
    _ = L * T ^ 3 / 6 *
          Real.exp (-((1 - c) * T ^ 2) / 2) := by
          rw [show
              L * Real.exp (-(T ^ 2) / 2) *
                  (T ^ 3 / 6 * Real.exp (c * T ^ 2 / 2)) =
                L * T ^ 3 / 6 *
                  (Real.exp (-(T ^ 2) / 2) *
                    Real.exp (c * T ^ 2 / 2)) by ring,
            ← Real.exp_add]
          congr 2
          ring

/--
On the second branch, both inner integrals admit explicit endpoint bounds.
This removes the final nested quadrature from `tyurinDeltaTwo`.
-/
theorem tyurinDeltaTwo_le_secondClosed
    {L t : ℝ} (hL : 0 < L)
    (hbranch : ¬ |t| * lyapunovThirdRoot L ≤ 5 / 3) :
    let T := |t|
    let R := lyapunovThirdRoot L
    let A := 5 / (3 * R)
    tyurinDeltaTwo L t ≤
      L * A ^ 3 / 6 *
          Real.exp (-(T ^ 2) / 2 +
            lyapunovVarianceCap L * A ^ 2 / 2) +
        L * (T ^ 3 - A ^ 3) /
            (6 * tyurinRationalEll) *
          Real.exp (-(T ^ 2) / 2 + L * T ^ 3 / 5) := by
  dsimp only
  let T : ℝ := |t|
  let R : ℝ := lyapunovThirdRoot L
  let A : ℝ := 5 / (3 * R)
  have hL0 : 0 ≤ L := hL.le
  have hT : 0 ≤ T := abs_nonneg _
  have hR : 0 < R := by
    unfold R lyapunovThirdRoot
    positivity
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hAT : A ≤ T := by
    have hstrict : 5 / 3 < T * R := by
      simpa [T, R, not_le] using hbranch
    unfold A
    rw [div_le_iff₀ (by positivity : 0 < 3 * R)]
    nlinarith
  have hc : 0 ≤ lyapunovVarianceCap L :=
    lyapunovVarianceCap_nonneg hL0
  have hFirst :=
    integral_sq_div_two_mul_exp_sq_le hA hc
  have hSecond :=
    integral_sq_div_two_mul_exp_cube_le hA hAT hL0
  have hEll : 0 < tyurinRationalEll := by
    unfold tyurinRationalEll
    positivity
  unfold tyurinDeltaTwo
  dsimp only
  rw [if_neg hbranch]
  change
    L * Real.exp (-(T ^ 2) / 2) *
        ((∫ s : ℝ in 0..A,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) +
          ∫ s : ℝ in A..T,
            s ^ 2 / (2 * tyurinRationalEll) *
              Real.exp (L * s ^ 3 / 5)) ≤ _
  have hSecondScaled :
      (∫ s : ℝ in A..T,
          s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5)) ≤
        (T ^ 3 - A ^ 3) /
            (6 * tyurinRationalEll) *
          Real.exp (L * T ^ 3 / 5) := by
    have hRewrite :
        (fun s : ℝ =>
          s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5)) =
          fun s : ℝ =>
            (1 / tyurinRationalEll) *
              (s ^ 2 / 2 * Real.exp (L * s ^ 3 / 5)) := by
      funext s
      field_simp [hEll.ne']
    rw [hRewrite, intervalIntegral.integral_const_mul]
    calc
      (1 / tyurinRationalEll) *
          (∫ s : ℝ in A..T,
            s ^ 2 / 2 * Real.exp (L * s ^ 3 / 5))
          ≤ (1 / tyurinRationalEll) *
              ((T ^ 3 - A ^ 3) / 6 *
                Real.exp (L * T ^ 3 / 5)) := by
            gcongr
      _ = (T ^ 3 - A ^ 3) /
              (6 * tyurinRationalEll) *
            Real.exp (L * T ^ 3 / 5) := by
            field_simp [hEll.ne']
  calc
    L * Real.exp (-(T ^ 2) / 2) *
        ((∫ s : ℝ in 0..A,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) +
          ∫ s : ℝ in A..T,
            s ^ 2 / (2 * tyurinRationalEll) *
              Real.exp (L * s ^ 3 / 5))
        ≤ L * Real.exp (-(T ^ 2) / 2) *
            (A ^ 3 / 6 *
                Real.exp
                  (lyapunovVarianceCap L * A ^ 2 / 2) +
              (T ^ 3 - A ^ 3) /
                  (6 * tyurinRationalEll) *
                Real.exp (L * T ^ 3 / 5)) := by
          gcongr
    _ = L * A ^ 3 / 6 *
            Real.exp (-(T ^ 2) / 2 +
              lyapunovVarianceCap L * A ^ 2 / 2) +
          L * (T ^ 3 - A ^ 3) /
              (6 * tyurinRationalEll) *
            Real.exp (-(T ^ 2) / 2 + L * T ^ 3 / 5) := by
          rw [Real.exp_add, Real.exp_add]
          field_simp [hEll.ne']

/-! ## Finite certificate-facing discrepancy envelopes -/

/--
Finite right-sum upper envelope for `tyurinDeltaOne`.
-/
noncomputable def tyurinDeltaOneRiemannUpper
    (n : ℕ) (L t : ℝ) : ℝ :=
  L * Real.exp (-(|t| ^ 2) / 2) *
    sqExpSqRightSum n 1 |t|

/--
Finite right-sum upper envelope for `tyurinDeltaTwo`.
-/
noncomputable def tyurinDeltaTwoRiemannUpper
    (n : ℕ) (L t : ℝ) : ℝ :=
  let T := |t|
  let R := lyapunovThirdRoot L
  let A := 5 / (3 * R)
  if T * R ≤ 5 / 3 then
    L * Real.exp (-(T ^ 2) / 2) *
      sqExpSqRightSum n (lyapunovVarianceCap L) T
  else
    L * Real.exp (-(T ^ 2) / 2) *
      (sqExpSqRightSum n (lyapunovVarianceCap L) A +
        (1 / tyurinRationalEll) *
          sqExpCubeRightSum n L A T)

/--
Finite trapezoidal upper envelope for `tyurinDeltaOne`.
-/
noncomputable def tyurinDeltaOneTrapezoidUpper
    (n : ℕ) (L t : ℝ) : ℝ :=
  L * Real.exp (-(|t| ^ 2) / 2) *
    sqExpSqTrapezoid n 1 |t|

/--
Finite trapezoidal upper envelope for `tyurinDeltaTwo`.
-/
noncomputable def tyurinDeltaTwoTrapezoidUpper
    (n : ℕ) (L t : ℝ) : ℝ :=
  let T := |t|
  let R := lyapunovThirdRoot L
  let A := 5 / (3 * R)
  if T * R ≤ 5 / 3 then
    L * Real.exp (-(T ^ 2) / 2) *
      sqExpSqTrapezoid n (lyapunovVarianceCap L) T
  else
    L * Real.exp (-(T ^ 2) / 2) *
      (sqExpSqTrapezoid n (lyapunovVarianceCap L) A +
        (1 / tyurinRationalEll) *
          sqExpCubeTrapezoid n L A T)

theorem tyurinDeltaOne_le_riemannUpper
    {n : ℕ} {L t : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    tyurinDeltaOne L t ≤
      tyurinDeltaOneRiemannUpper n L t := by
  have hIntegral :=
    integral_sq_div_two_mul_exp_sq_le_rightSum
      (n := n) hn (abs_nonneg t) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold tyurinDeltaOne tyurinDeltaOneRiemannUpper
  have hfront :
      0 ≤ L * Real.exp (-(|t| ^ 2) / 2) := by
    positivity
  apply mul_le_mul_of_nonneg_left _ hfront
  simpa using hIntegral

theorem tyurinDeltaTwo_le_riemannUpper
    {n : ℕ} {L t : ℝ} (hn : 0 < n) (hL : 0 < L) :
    tyurinDeltaTwo L t ≤
      tyurinDeltaTwoRiemannUpper n L t := by
  let T : ℝ := |t|
  let R : ℝ := lyapunovThirdRoot L
  let A : ℝ := 5 / (3 * R)
  have hL0 : 0 ≤ L := hL.le
  have hT : 0 ≤ T := abs_nonneg _
  have hR : 0 < R := by
    unfold R lyapunovThirdRoot
    positivity
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hc : 0 ≤ lyapunovVarianceCap L :=
    lyapunovVarianceCap_nonneg hL0
  have hfront :
      0 ≤ L * Real.exp (-(T ^ 2) / 2) := by
    positivity
  unfold tyurinDeltaTwo tyurinDeltaTwoRiemannUpper
  dsimp only
  by_cases hbranch : T * R ≤ 5 / 3
  · rw [if_pos hbranch, if_pos hbranch]
    apply mul_le_mul_of_nonneg_left _ hfront
    exact integral_sq_div_two_mul_exp_sq_le_rightSum
      hn hT hc
  · rw [if_neg hbranch, if_neg hbranch]
    have hAT : A ≤ T := by
      have hstrict : 5 / 3 < T * R := lt_of_not_ge hbranch
      unfold A
      rw [div_le_iff₀ (by positivity : 0 < 3 * R)]
      nlinarith
    have hFirst :
        (∫ s : ℝ in 0..A,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) ≤
          sqExpSqRightSum n (lyapunovVarianceCap L) A :=
      integral_sq_div_two_mul_exp_sq_le_rightSum hn hA hc
    have hSecond :
        (∫ s : ℝ in A..T,
            s ^ 2 / 2 * Real.exp (L * s ^ 3 / 5)) ≤
          sqExpCubeRightSum n L A T :=
      integral_sq_div_two_mul_exp_cube_le_rightSum
        hn hA hAT hL0
    have hEll : 0 < tyurinRationalEll := by
      unfold tyurinRationalEll
      positivity
    apply mul_le_mul_of_nonneg_left _ hfront
    apply add_le_add hFirst
    have hRewrite :
        (fun s : ℝ =>
          s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5)) =
          fun s : ℝ =>
            (1 / tyurinRationalEll) *
              (s ^ 2 / 2 * Real.exp (L * s ^ 3 / 5)) := by
      funext s
      field_simp [hEll.ne']
    rw [hRewrite, intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hSecond (by positivity)

theorem tyurinDeltaOne_le_trapezoidUpper
    {n : ℕ} {L t : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    tyurinDeltaOne L t ≤
      tyurinDeltaOneTrapezoidUpper n L t := by
  have hIntegral :=
    integral_sq_div_two_mul_exp_sq_le_trapezoid
      (n := n) hn (abs_nonneg t) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold tyurinDeltaOne tyurinDeltaOneTrapezoidUpper
  have hfront :
      0 ≤ L * Real.exp (-(|t| ^ 2) / 2) := by
    positivity
  apply mul_le_mul_of_nonneg_left _ hfront
  simpa using hIntegral

theorem tyurinDeltaTwo_le_trapezoidUpper
    {n : ℕ} {L t : ℝ} (hn : 0 < n) (hL : 0 < L) :
    tyurinDeltaTwo L t ≤
      tyurinDeltaTwoTrapezoidUpper n L t := by
  let T : ℝ := |t|
  let R : ℝ := lyapunovThirdRoot L
  let A : ℝ := 5 / (3 * R)
  have hL0 : 0 ≤ L := hL.le
  have hT : 0 ≤ T := abs_nonneg _
  have hR : 0 < R := by
    unfold R lyapunovThirdRoot
    positivity
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hc : 0 ≤ lyapunovVarianceCap L :=
    lyapunovVarianceCap_nonneg hL0
  have hfront :
      0 ≤ L * Real.exp (-(T ^ 2) / 2) := by
    positivity
  unfold tyurinDeltaTwo tyurinDeltaTwoTrapezoidUpper
  dsimp only
  by_cases hbranch : T * R ≤ 5 / 3
  · rw [if_pos hbranch, if_pos hbranch]
    apply mul_le_mul_of_nonneg_left _ hfront
    exact integral_sq_div_two_mul_exp_sq_le_trapezoid
      hn hT hc
  · rw [if_neg hbranch, if_neg hbranch]
    have hAT : A ≤ T := by
      have hstrict : 5 / 3 < T * R := lt_of_not_ge hbranch
      unfold A
      rw [div_le_iff₀ (by positivity : 0 < 3 * R)]
      nlinarith
    have hFirst :
        (∫ s : ℝ in 0..A,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) ≤
          sqExpSqTrapezoid n (lyapunovVarianceCap L) A :=
      integral_sq_div_two_mul_exp_sq_le_trapezoid hn hA hc
    have hSecond :
        (∫ s : ℝ in A..T,
            s ^ 2 / 2 * Real.exp (L * s ^ 3 / 5)) ≤
          sqExpCubeTrapezoid n L A T :=
      integral_sq_div_two_mul_exp_cube_le_trapezoid
        hn hA hAT hL0
    have hEll : 0 < tyurinRationalEll := by
      unfold tyurinRationalEll
      positivity
    apply mul_le_mul_of_nonneg_left _ hfront
    apply add_le_add hFirst
    have hRewrite :
        (fun s : ℝ =>
          s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5)) =
          fun s : ℝ =>
            (1 / tyurinRationalEll) *
              (s ^ 2 / 2 * Real.exp (L * s ^ 3 / 5)) := by
      funext s
      field_simp [hEll.ne']
    rw [hRewrite, intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hSecond (by positivity)

end Probability
end CertifiedJL
