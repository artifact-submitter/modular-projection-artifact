/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Core
import CertifiedJL.Certificates.Shared.UpperContourSoundness
import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContour
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContourQuadrature
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperRealDeficit
import CertifiedJL.Probability.NormalApproximation.Lyapunov.ModerateLyapunov

/-!
# Shared analytic facts for sparse upper-contour certificates

This module connects the sparse executable cap to the literal U8 function.
It is kept outside `Core` so the numerical evaluator has no dependency on the
analytic sparse-row development.
-/

namespace CertifiedJL
namespace SparseUpperContour

set_option maxRecDepth 100000

open MeasureTheory ProbabilityTheory Set

/-- Sparse-specific public API bridge: the executable kernel's factored U4
value is exactly the established analytic contour majorant. -/
theorem normalizedFourthOrderRowBound_eq_sparseUpperMajorant
    (profile lambda : ℚ) (frequency : ℝ) (hlambda : (lambda : ℝ) < 1) :
    UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
        profile lambda frequency =
      sparseUpperFourthOrderNormalizedMajorant
        (profile : ℝ) (lambda : ℝ) frequency := by
  simpa [rowCoefficients, UpperContourKernel.canonicalSparseFourthOrderNormalizedMajorant,
    sparseUpperFourthOrderNormalizedMajorant] using
    UpperContourKernel.normalizedFourthOrderRowBound_sparse_eq_canonical
      profile lambda frequency hlambda

private theorem lowerRat_le_of_contains {p : ℕ} {I : Interval p} {x : ℝ}
    (h : I.Contains x) : (I.lowerRat : ℝ) ≤ x := by
  simpa only [Interval.lowerRat, Dyadic.cast_toRat] using h.1

theorem Internal.toReal_mono {p : ℕ} {a b : ℤ} (h : a ≤ b) :
    Dyadic.toReal p a ≤ Dyadic.toReal p b := by
  unfold Dyadic.toReal
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

private theorem toReal_scale (p : ℕ) :
    Dyadic.toReal p (Dyadic.scale p : ℤ) = 1 := by
  simp [Dyadic.toReal]

private theorem toReal_min (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (min a b) = min (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (Internal.toReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (Internal.toReal_mono h')]

private theorem toReal_max (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (max a b) = max (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (Internal.toReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (Internal.toReal_mono h')]

theorem Internal.contains_foldl_add
    {p : ℕ} {A : Type*} (xs : List A)
    (F : A → Interval p) (f : A → ℝ)
    (hF : ∀ i ∈ xs, (F i).Contains (f i))
    {I : Interval p} {x : ℝ} (hI : I.Contains x) :
    (xs.foldl (fun acc i ↦ acc + F i) I).Contains
      (xs.foldl (fun acc i ↦ acc + f i) x) := by
  induction xs generalizing I x with
  | nil => exact hI
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hF j (List.mem_cons_of_mem i hj)
      · exact Interval.contains_add hI (hF i (by simp))

theorem Internal.foldl_add_eq_add_sum_map
    {A : Type*} (xs : List A) (f : A → ℝ) (x : ℝ) :
    xs.foldl (fun acc i ↦ acc + f i) x = x + (xs.map f).sum := by
  induction xs generalizing x with
  | nil => simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring

theorem Internal.finset_sum_range_eq_list_sum_map
    (n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, List.range_succ, ih]

theorem Internal.sum_map_sum_eq_sum_flatMap
    {A B : Type*} (xs : List A) (g : A → List B) (f : B → ℝ) :
    (xs.map (fun x ↦ ((g x).map f).sum)).sum =
      ((xs.flatMap g).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.sum_append]

theorem Internal.realRowDeficitCap_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ realRowDeficitCap v := by
  unfold realRowDeficitCap
  positivity

private theorem realRowDeficitCap_le_one {v : ℝ} (hv : 0 ≤ v) :
    realRowDeficitCap v ≤ 1 := by
  have h := antitoneOn_realRowDeficitCap (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show v ∈ Set.Ici 0 by simpa) hv
  simpa [realRowDeficitCap] using h

/-- The executable U8 cap upper-bounds the literal cap at every real profile
to the right of the box's left endpoint. The side conditions are precisely
the positivity and scaling facts used by square root, reciprocal, and the
positive-exponential enclosure. -/
theorem upperBounds_realCapUpper
    (p : ℕ) (profileLeft lam : ℚ) (profile : ℝ)
    (hprofileLeft : 0 ≤ profileLeft)
    (hprofile : (profileLeft : ℝ) ≤ profile)
    (hlam : 0 ≤ lam) (hlamOne : lam < 1)
    (hsqrtInput : 0 ≤ (UpperContourKernel.frac p profileLeft).lo)
    (hexponentUpper :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      exponent < (2 ^ 30 : ℕ))
    (hexponentBase :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      0 < (Interval.ofRat p (1 - exponent / (2 ^ 30 : ℕ))).lo)
    (hdenominatorInput :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 ≤ (UpperContourKernel.frac p (1 + argument)).lo)
    (hdenominator :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 < (UpperContourKernel.frac p 2 *
        (UpperContourKernel.frac p (1 + argument)).sqrt).lo) :
    realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ))) ≤
      Dyadic.toReal p (realCapUpper p profileLeft lam).hi := by
  have hlamReal : 0 ≤ (lam : ℝ) := by exact_mod_cast hlam
  have hlamOneReal : (lam : ℝ) < 1 := by exact_mod_cast hlamOne
  have hprofileLeftReal : (0 : ℝ) ≤ profileLeft := by
    exact_mod_cast hprofileLeft
  have hprofileNonneg : 0 ≤ profile := hprofileLeftReal.trans hprofile
  let actualArgument :=
    Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ))
  have hactualArgument : 0 ≤ actualArgument := by
    dsimp only [actualArgument]
    positivity
  have hone := realRowDeficitCap_le_one hactualArgument
  by_cases hzero : profileLeft = 0
  · rw [realCapUpper, if_pos hzero]
    rw [toReal_scale]
    exact hone
  · let squareRoot := (UpperContourKernel.frac p profileLeft).sqrt
    let squareRootLower := squareRoot.lowerRat
    let argument := squareRootLower * lam / (1 - lam)
    let exponent := argument / (1 + argument)
    let numerator := UpperContourKernel.one p + Exp.posUpper p exponent 30
    let denominator := UpperContourKernel.frac p 2 *
      (UpperContourKernel.frac p (1 + argument)).sqrt
    let result := UpperContourKernel.divide numerator denominator
    have hleftValue : (UpperContourKernel.frac p profileLeft).Contains
        (profileLeft : ℝ) := Interval.contains_ofRat p profileLeft
    have hsqrt : squareRoot.Contains (Real.sqrt (profileLeft : ℝ)) :=
      Interval.contains_sqrt hsqrtInput hleftValue
    have hsqrtLower : (squareRootLower : ℝ) ≤ Real.sqrt profile := by
      calc
        (squareRootLower : ℝ) ≤ Real.sqrt (profileLeft : ℝ) :=
          lowerRat_le_of_contains hsqrt
        _ ≤ Real.sqrt profile := Real.sqrt_le_sqrt hprofile
    have hsqrtLowerNonneg : 0 ≤ (squareRootLower : ℝ) := by
      dsimp only [squareRootLower, squareRoot, Interval.lowerRat,
        Interval.sqrt, Dyadic.toRat]
      positivity
    have hargumentNonneg : 0 ≤ (argument : ℝ) := by
      dsimp only [argument]
      push_cast
      positivity
    have hargument : (argument : ℝ) ≤ actualArgument := by
      dsimp only [argument, actualArgument]
      push_cast
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsqrtLower hlamReal)
        (sub_nonneg.mpr hlamOneReal.le)
    have hcapMonotone : realRowDeficitCap actualArgument ≤
        realRowDeficitCap (argument : ℝ) :=
      antitoneOn_realRowDeficitCap (by simpa using hargumentNonneg)
        (by simpa using hactualArgument) hargument
    have hexponentNonneg : 0 ≤ exponent := by
      dsimp only [exponent]
      have hargumentRat : 0 ≤ argument := by exact_mod_cast hargumentNonneg
      exact div_nonneg hargumentRat (by positivity)
    have hexponential : (Exp.posUpper p exponent 30).Contains
        (Real.exp (exponent : ℝ)) :=
      Exp.posUpper_contains hexponentNonneg hexponentUpper hexponentBase
    have hnumerator : numerator.Contains
        (1 + Real.exp (exponent : ℝ)) := by
      exact Interval.contains_add
        (by simpa [UpperContourKernel.one, UpperContourKernel.frac] using
          Interval.contains_ofRat p (1 : ℚ)) hexponential
    have hdenominatorSqrt :
        (UpperContourKernel.frac p (1 + argument)).sqrt.Contains
          (Real.sqrt (1 + (argument : ℝ))) :=
      Interval.contains_sqrt hdenominatorInput
        (by simpa [UpperContourKernel.frac] using
          Interval.contains_ofRat p (1 + argument))
    have hdenominatorValue : denominator.Contains
        (2 * Real.sqrt (1 + (argument : ℝ))) := by
      exact Interval.contains_mul
        (by simpa [UpperContourKernel.frac] using
          Interval.contains_ofRat p (2 : ℚ)) hdenominatorSqrt
    have hresult : result.Contains (realRowDeficitCap (argument : ℝ)) := by
      simpa [result, numerator, denominator, realRowDeficitCap, exponent] using
        UpperContourKernel.contains_divide_of_pos hdenominator hnumerator
          hdenominatorValue
    rw [realCapUpper, if_neg hzero]
    change realRowDeficitCap actualArgument ≤
      Dyadic.toReal p (min (Dyadic.scale p : ℤ) result.hi)
    have hmin : Dyadic.toReal p (min (Dyadic.scale p : ℤ) result.hi) =
        min 1 (Dyadic.toReal p result.hi) := by
      by_cases horder : (Dyadic.scale p : ℤ) ≤ result.hi
      · rw [min_eq_left horder, min_eq_left]
        · exact toReal_scale p
        · simpa [toReal_scale] using Internal.toReal_mono (p := p) horder
      · have horder' : result.hi ≤ (Dyadic.scale p : ℤ) :=
          le_of_not_ge horder
        rw [min_eq_right horder', min_eq_right]
        simpa [toReal_scale] using Internal.toReal_mono (p := p) horder'
    rw [hmin]
    exact le_min hone (hcapMonotone.trans hresult.2)

/-- Away from the zero-left endpoint, `realCapUpper` is a full interval
enclosure of the literal U8 cap, not only an upper-endpoint statement. -/
theorem contains_realCapUpper_of_ne_zero
    (p : ℕ) (profileLeft lam : ℚ) (profile : ℝ)
    (hprofileLeft : 0 ≤ profileLeft) (hprofileLeftNe : profileLeft ≠ 0)
    (hprofile : (profileLeft : ℝ) ≤ profile)
    (hlam : 0 ≤ lam) (hlamOne : lam < 1)
    (hsqrtInput : 0 ≤ (UpperContourKernel.frac p profileLeft).lo)
    (hexponentUpper :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      exponent < (2 ^ 30 : ℕ))
    (hexponentBase :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      0 < (Interval.ofRat p (1 - exponent / (2 ^ 30 : ℕ))).lo)
    (hdenominatorInput :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 ≤ (UpperContourKernel.frac p (1 + argument)).lo)
    (hdenominator :
      let squareRootLower :=
        (UpperContourKernel.frac p profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 < (UpperContourKernel.frac p 2 *
        (UpperContourKernel.frac p (1 + argument)).sqrt).lo) :
    (realCapUpper p profileLeft lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ)))) := by
  have hu := upperBounds_realCapUpper p profileLeft lam profile hprofileLeft
    hprofile hlam hlamOne hsqrtInput hexponentUpper hexponentBase
      hdenominatorInput hdenominator
  constructor
  · rw [realCapUpper, if_neg hprofileLeftNe]
    simp only [Dyadic.toReal_zero]
    have hprofileNonneg : 0 ≤ profile := by
      have hleftReal : (0 : ℝ) ≤ profileLeft := by exact_mod_cast hprofileLeft
      exact hleftReal.trans hprofile
    have hlamReal : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
    have hdenominatorReal : (0 : ℝ) ≤ 1 - (lam : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hlamOne.le)
    exact Internal.realRowDeficitCap_nonneg
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlamReal) hdenominatorReal)
  · exact hu

/-- The literal real value evaluated by the independent high-profile
certificate, including the `2^192` scaling used by its strict endpoint check. -/
noncomputable def highProfileScaledEndpoint (profile : ℝ) : ℝ :=
  let lam : ℚ := 583 / 1000
  (2 ^ securityBits : ℝ) * Real.exp (-(lam * threshold : ℚ)) *
    ((1 / (1 - lam) ^ (rows / 2) : ℚ) : ℝ) *
    realRowDeficitCap
      (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ))) ^ rows

/-- The checked high-profile interval encloses its literal scaled U8/Chernoff
endpoint for every profile at least `1/20`. -/
theorem highProfileBound_contains_scaledEndpoint
    {profile : ℝ} (hprofile : (1 / 20 : ℝ) ≤ profile) :
    highProfileBound.Contains (highProfileScaledEndpoint profile) := by
  let lam : ℚ := 583 / 1000
  have hcap : (realCapUpper highProfilePrecision (1 / 20) lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ)))) := by
    apply contains_realCapUpper_of_ne_zero
    · norm_num
    · norm_num
    · norm_num at hprofile ⊢
      exact hprofile
    · norm_num [lam]
    · norm_num [lam]
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  have hscaledExponential := UpperContourKernel.scaledNegExpUpper_contains
    highProfilePrecision 12 (lam * threshold) 34 4
      (by norm_num [lam, threshold])
  have hgaussian := Interval.contains_ofRat highProfilePrecision
    (1 / (1 - lam) ^ (rows / 2) : ℚ)
  have hcapPower := Interval.contains_squareN hcap 9
  have hproduct := Interval.contains_mul
    (Interval.contains_mul hscaledExponential hgaussian) hcapPower
  simpa [highProfileBound, highProfileScaledEndpoint, lam, rows,
    securityBits, UpperContourKernel.frac,
    Interval.iterSquare_eq_pow_two_pow] using hproduct

/-- The kernel-checked high-profile replay turns its literal scaled endpoint
into a strict real inequality. -/
theorem highProfileScaledEndpoint_lt_half
    {profile : ℝ} (hprofile : (1 / 20 : ℝ) ≤ profile)
    (hverified : highProfileBound.upperRat < 1 / 2) :
    highProfileScaledEndpoint profile < 1 / 2 := by
  have hcontains := highProfileBound_contains_scaledEndpoint hprofile
  calc
    highProfileScaledEndpoint profile ≤
        (highProfileBound.upperRat : ℝ) := by
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2
    _ < 1 / 2 := by
      have hreal : (highProfileBound.upperRat : ℝ) < (((1 / 2 : ℚ) : ℝ)) := by
        exact_mod_cast hverified
      simpa using hreal

/-! ## Low-profile cell, tail, and prefactor boundary -/

private noncomputable def expNegTaylor0 (x : ℝ) : ℝ := Real.exp (-x) - 1
private noncomputable def expNegTaylor1 (x : ℝ) : ℝ := Real.exp (-x) - (1 - x)
private noncomputable def expNegTaylor2 (x : ℝ) : ℝ :=
  Real.exp (-x) - (1 - x + x ^ 2 / 2)
private noncomputable def expNegTaylor3 (x : ℝ) : ℝ :=
  Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6)
private noncomputable def expNegTaylor4 (x : ℝ) : ℝ :=
  Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24)
private noncomputable def expNegTaylor5 (x : ℝ) : ℝ :=
  Real.exp (-x) -
    (1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120)

private theorem nonneg_of_deriv_neg_nonpos
    {f g : ℝ → ℝ} (hf0 : f 0 = 0)
    (hderiv : ∀ x, HasDerivAt f (-g x) x)
    (hg : ∀ x, 0 ≤ x → g x ≤ 0) :
    ∀ x, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun y _ ↦ (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hderiv y).hasDerivWithinAt)
      (fun y hy ↦ neg_nonneg.mpr (hg y (interior_subset hy)))
  calc
    0 = f 0 := hf0.symm
    _ ≤ f x := hmono (by simp) hx hx

private theorem nonpos_of_deriv_neg_nonneg
    {f g : ℝ → ℝ} (hf0 : f 0 = 0)
    (hderiv : ∀ x, HasDerivAt f (-g x) x)
    (hg : ∀ x, 0 ≤ x → 0 ≤ g x) :
    ∀ x, 0 ≤ x → f x ≤ 0 := by
  intro x hx
  have hanti : AntitoneOn f (Set.Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
      (fun y _ ↦ (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hderiv y).hasDerivWithinAt)
      (fun y hy ↦ neg_nonpos.mpr (hg y (interior_subset hy)))
  calc
    f x ≤ f 0 := hanti (by simp) hx hx
    _ = 0 := hf0

/-- The odd fifth Taylor polynomial is a global lower bound for `exp (-x)`
on the nonnegative half-line. This is the analytic fact used by `phiLower`. -/
theorem expNegTaylor5_le_exp_neg {x : ℝ} (hx : 0 ≤ x) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 ≤
      Real.exp (-x) := by
  have hderiv0 : ∀ y, HasDerivAt expNegTaylor0 (-Real.exp (-y)) y := by
    intro y
    change HasDerivAt (fun z : ℝ ↦ Real.exp (-z) - 1) (-Real.exp (-y)) y
    convert (((Real.hasDerivAt_exp (-y)).comp y
      (hasDerivAt_id y).neg).sub_const 1) using 1
    all_goals first | assumption | rfl | ring
  have h0 : ∀ y, 0 ≤ y → expNegTaylor0 y ≤ 0 := by
    intro y hy
    simp only [expNegTaylor0, sub_nonpos]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)
  have hderiv1 : ∀ y, HasDerivAt expNegTaylor1 (-expNegTaylor0 y) y := by
    intro y
    change HasDerivAt (fun z : ℝ ↦ Real.exp (-z) - (1 - z))
      (-(Real.exp (-y) - 1)) y
    convert (((Real.hasDerivAt_exp (-y)).comp y
      (hasDerivAt_id y).neg).sub
        ((hasDerivAt_const y 1).sub (hasDerivAt_id y))) using 1
    all_goals first | assumption | rfl | ring
  have h1 : ∀ y, 0 ≤ y → 0 ≤ expNegTaylor1 y :=
    nonneg_of_deriv_neg_nonpos (by simp [expNegTaylor1]) hderiv1 h0
  have hderiv2 : ∀ y, HasDerivAt expNegTaylor2 (-expNegTaylor1 y) y := by
    intro y
    change HasDerivAt
      (fun z : ℝ ↦ Real.exp (-z) - (1 - z + z ^ 2 / 2))
      (-(Real.exp (-y) - (1 - y))) y
    convert (((Real.hasDerivAt_exp (-y)).comp y
      (hasDerivAt_id y).neg).sub
        (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2))) using 1
    all_goals first | assumption | rfl | ring
  have h2 : ∀ y, 0 ≤ y → expNegTaylor2 y ≤ 0 :=
    nonpos_of_deriv_neg_nonneg (by simp [expNegTaylor2]) hderiv2 h1
  have hderiv3 : ∀ y, HasDerivAt expNegTaylor3 (-expNegTaylor2 y) y := by
    intro y
    change HasDerivAt
      (fun z : ℝ ↦ Real.exp (-z) -
        (1 - z + z ^ 2 / 2 - z ^ 3 / 6))
      (-(Real.exp (-y) - (1 - y + y ^ 2 / 2))) y
    convert (((Real.hasDerivAt_exp (-y)).comp y
      (hasDerivAt_id y).neg).sub
        ((((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2)).sub
            ((hasDerivAt_pow 3 y).div_const 6))) using 1
    all_goals first | assumption | rfl | ring
  have h3 : ∀ y, 0 ≤ y → 0 ≤ expNegTaylor3 y :=
    nonneg_of_deriv_neg_nonpos (by simp [expNegTaylor3]) hderiv3 h2
  have hderiv4 : ∀ y, HasDerivAt expNegTaylor4 (-expNegTaylor3 y) y := by
    intro y
    change HasDerivAt
      (fun z : ℝ ↦ Real.exp (-z) -
        (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24))
      (-(Real.exp (-y) -
        (1 - y + y ^ 2 / 2 - y ^ 3 / 6))) y
    convert (((Real.hasDerivAt_exp (-y)).comp y
      (hasDerivAt_id y).neg).sub
        (((((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2)).sub
            ((hasDerivAt_pow 3 y).div_const 6)).add
              ((hasDerivAt_pow 4 y).div_const 24))) using 1
    all_goals first | assumption | rfl | ring
  have h4 : ∀ y, 0 ≤ y → expNegTaylor4 y ≤ 0 :=
    nonpos_of_deriv_neg_nonneg (by simp [expNegTaylor4]) hderiv4 h3
  have hderiv5 : ∀ y, HasDerivAt expNegTaylor5 (-expNegTaylor4 y) y := by
    intro y
    change HasDerivAt
      (fun z : ℝ ↦ Real.exp (-z) -
        (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 - z ^ 5 / 120))
      (-(Real.exp (-y) -
        (1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24))) y
    convert (((Real.hasDerivAt_exp (-y)).comp y
      (hasDerivAt_id y).neg).sub
        ((((((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2)).sub
            ((hasDerivAt_pow 3 y).div_const 6)).add
              ((hasDerivAt_pow 4 y).div_const 24)).sub
                ((hasDerivAt_pow 5 y).div_const 120))) using 1
    all_goals first | assumption | rfl | ring
  have h5 : 0 ≤ expNegTaylor5 x :=
    nonneg_of_deriv_neg_nonpos (by simp [expNegTaylor5]) hderiv5 h4 x hx
  simpa [expNegTaylor5, sub_nonneg] using h5

private noncomputable def gaussianPhiPolynomial (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 40 - x ^ 7 / 336 +
    x ^ 9 / 3456 - x ^ 11 / 42240

private noncomputable def gaussianDensityPolynomial (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + (x ^ 2 / 2) ^ 2 / 2 -
    (x ^ 2 / 2) ^ 3 / 6 + (x ^ 2 / 2) ^ 4 / 24 -
      (x ^ 2 / 2) ^ 5 / 120

private theorem hasDerivAt_gaussianPhiPolynomial (x : ℝ) :
    HasDerivAt gaussianPhiPolynomial (gaussianDensityPolynomial x) x := by
  change HasDerivAt
    (fun z : ℝ ↦ z - z ^ 3 / 6 + z ^ 5 / 40 - z ^ 7 / 336 +
      z ^ 9 / 3456 - z ^ 11 / 42240)
    (1 - x ^ 2 / 2 + (x ^ 2 / 2) ^ 2 / 2 -
      (x ^ 2 / 2) ^ 3 / 6 + (x ^ 2 / 2) ^ 4 / 24 -
        (x ^ 2 / 2) ^ 5 / 120) x
  convert ((((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
    ((hasDerivAt_pow 5 x).div_const 40)).sub
      ((hasDerivAt_pow 7 x).div_const 336)).add
        ((hasDerivAt_pow 9 x).div_const 3456)).sub
          ((hasDerivAt_pow 11 x).div_const 42240)) using 1
  all_goals first | assumption | rfl | ring

private theorem cast_phiLower_eq (value : ℚ) :
    ((UpperContourKernel.phiLower value : ℚ) : ℝ) =
      1 / 2 + (199 / 500 : ℝ) * gaussianPhiPolynomial (value : ℝ) := by
  norm_num [UpperContourKernel.phiLower, List.range_succ, gaussianPhiPolynomial]
  ring

private theorem standardGaussianCDF_eq_half_add_integral_density
    {theta : ℝ} (htheta : 0 ≤ theta) :
    standardGaussianCDF theta =
      1 / 2 + ∫ x : ℝ in Set.Ioc 0 theta,
        Probability.standardGaussianDensity x := by
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) theta) (Set.Ioi theta) := by
    exact Set.disjoint_left.2 fun x hx hxt ↦ (not_lt_of_ge hx.2) hxt
  have hunion : Set.Ioc (0 : ℝ) theta ∪ Set.Ioi theta = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact lt_of_le_of_lt htheta hx
    · intro hx
      by_cases hxt : x ≤ theta
      · exact Or.inl ⟨hx, hxt⟩
      · exact Or.inr (lt_of_not_ge hxt)
  have hdecomp :
      Probability.standardGaussianTail 0 =
        (∫ x : ℝ in Set.Ioc 0 theta,
          Probability.standardGaussianDensity x) +
          Probability.standardGaussianTail theta := by
    unfold Probability.standardGaussianTail
    rw [← setIntegral_union hdisjoint measurableSet_Ioi
      Probability.integrable_standardGaussianDensity.integrableOn
      Probability.integrable_standardGaussianDensity.integrableOn, hunion]
  change cdf (ProbabilityTheory.gaussianReal 0 1) theta = _
  rw [Probability.cdf_standardGaussian_eq_one_sub_tail]
  rw [Probability.standardGaussianTail_zero] at hdecomp
  linarith

private theorem gaussianDensityPolynomial_nonneg
    {x : ℝ} (hx : 0 ≤ x) (hxUpper : x ≤ 1) :
    0 ≤ gaussianDensityPolynomial x := by
  let y := x ^ 2 / 2
  have hy : 0 ≤ y := by dsimp only [y]; positivity
  have hyOne : y ≤ 1 := by
    dsimp only [y]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hxUpper)]
  have h1 : 0 ≤ 1 - y := sub_nonneg.mpr hyOne
  have h2 : 0 ≤ y ^ 2 * (1 / 2 - y / 6) := by
    apply mul_nonneg (sq_nonneg y)
    nlinarith
  have h3 : 0 ≤ y ^ 4 * (1 / 24 - y / 120) := by
    apply mul_nonneg (Even.pow_nonneg (even_two_mul 2) y)
    nlinarith
  dsimp only [gaussianDensityPolynomial, y] at h1 h2 h3 ⊢
  nlinarith

private theorem gaussianDensityPolynomial_le_density
    {x : ℝ} (hx : 0 ≤ x) (hxUpper : x ≤ 1) :
    (199 / 500 : ℝ) * gaussianDensityPolynomial x ≤
      Probability.standardGaussianDensity x := by
  have hsqrtPos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hcoefficient : (199 / 500 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 199 / 500) hsqrtPos]
    nlinarith [sqrt_two_pi_lt_251_div_100]
  have hpolyNonneg := gaussianDensityPolynomial_nonneg hx hxUpper
  have htaylor : gaussianDensityPolynomial x ≤ Real.exp (-x ^ 2 / 2) := by
    unfold gaussianDensityPolynomial
    convert expNegTaylor5_le_exp_neg
      (show 0 ≤ x ^ 2 / 2 by positivity) using 1
    all_goals ring
  unfold Probability.standardGaussianDensity
  exact (mul_le_mul_of_nonneg_right hcoefficient.le hpolyNonneg).trans
    (mul_le_mul_of_nonneg_left htaylor (inv_nonneg.mpr hsqrtPos.le))

/-- The rational polynomial remains a genuine lower bound for the standard
Gaussian CDF throughout the larger shift range used by the high-security
family. -/
theorem phiLower_le_standardGaussianCDF_of_le_one
    (theta : ℚ) (htheta : 0 ≤ theta) (hthetaUpper : theta ≤ 1) :
    ((UpperContourKernel.phiLower theta : ℚ) : ℝ) ≤
      standardGaussianCDF (theta : ℝ) := by
  have hthetaReal : (0 : ℝ) ≤ theta := by exact_mod_cast htheta
  have hthetaUpperReal : (theta : ℝ) ≤ 1 := by
    have hcast : (theta : ℝ) ≤ (((1 : ℚ) : ℝ)) := by
      exact_mod_cast hthetaUpper
    norm_num at hcast ⊢
    exact hcast
  have hintegral :
      (199 / 500 : ℝ) * gaussianPhiPolynomial (theta : ℝ) ≤
        ∫ x : ℝ in Set.Ioc 0 (theta : ℝ),
          Probability.standardGaussianDensity x := by
    have hpolyIntegral :
        ∫ x : ℝ in Set.Ioc 0 (theta : ℝ),
            (199 / 500 : ℝ) * gaussianDensityPolynomial x =
          (199 / 500 : ℝ) * gaussianPhiPolynomial (theta : ℝ) := by
      rw [← intervalIntegral.integral_of_le hthetaReal]
      rw [intervalIntegral.integral_const_mul]
      have hint : IntervalIntegrable gaussianDensityPolynomial volume
          0 (theta : ℝ) := by
        have hcontinuous : Continuous gaussianDensityPolynomial := by
          unfold gaussianDensityPolynomial
          fun_prop
        exact hcontinuous.intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ ↦ hasDerivAt_gaussianPhiPolynomial x) hint]
      simp [gaussianPhiPolynomial]
    rw [← hpolyIntegral]
    apply setIntegral_mono_on
    · have hcontinuous : Continuous
          (fun x : ℝ ↦ (199 / 500 : ℝ) * gaussianDensityPolynomial x) := by
        unfold gaussianDensityPolynomial
        fun_prop
      exact hcontinuous.continuousOn.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    · exact Probability.integrable_standardGaussianDensity.integrableOn
    · exact measurableSet_Ioc
    · intro x hx
      exact gaussianDensityPolynomial_le_density hx.1.le
        (hx.2.trans hthetaUpperReal)
  rw [cast_phiLower_eq,
    standardGaussianCDF_eq_half_add_integral_density hthetaReal]
  linarith

/-- Backward-compatible specialization for the original sparse contour
parameter range. -/
theorem phiLower_le_standardGaussianCDF
    (theta : ℚ) (htheta : 0 ≤ theta) (hthetaUpper : theta ≤ 59 / 100) :
    ((UpperContourKernel.phiLower theta : ℚ) : ℝ) ≤
      standardGaussianCDF (theta : ℝ) :=
  phiLower_le_standardGaussianCDF_of_le_one theta htheta
    (hthetaUpper.trans (by norm_num))

/-- The decimal lower endpoint used in the certificate is strictly below
the true value of `pi`. -/
theorem piLower_lt_pi : (314159 / 100000 : ℝ) < Real.pi := by
  nlinarith [pi_gt_3141592_div_1000000]

/-- Elementary side conditions shared by the ten generated boxes. Keeping
this theorem finite makes the producer's exact parameter table explicit. -/
theorem profileBox_numeric_facts {box : ProfileBox}
    (hbox : box ∈ profileBoxes) :
    0 ≤ box.theta ∧ box.theta ≤ 59 / 100 ∧
    0 < UpperContourKernel.phiLower box.theta ∧
    0 < box.lam ∧ box.lam < 1 ∧ 0 < box.sigma ∧
    0 ≤ box.lam * (threshold - box.theta * box.sigma) -
      box.sigma * box.sigma * box.lam * box.lam / 2 ∧
    box.target < 1 := by
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with hbox | hbox | hbox | hbox | hbox | hbox | hbox | hbox | hbox | hbox <;>
    subst box <;>
    norm_num [UpperContourKernel.phiLower, List.range_succ, threshold]

/-- The literal prefactor in the positive-contour formula, including the
`2^192` endpoint scaling. -/
noncomputable def boxActualPrefactorValue (box : ProfileBox) : ℝ :=
  let exponent := box.lam * (threshold - box.theta * box.sigma) -
    box.sigma * box.sigma * box.lam * box.lam / 2
  (2 ^ securityBits : ℝ) * (1 / Real.pi) *
    (1 / standardGaussianCDF (box.theta : ℝ)) *
    Real.exp (-(exponent : ℚ)) *
    ((1 / (1 - box.lam) ^ (rows / 2) : ℚ) : ℝ)

private theorem mul_sqrt_eq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · rw [Real.sqrt_eq_rpow]
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    norm_num

/-- For fixed contour coordinates, the canonical normalized U4 expression
is convex in the nonnegative profile. This is the semantic reason the
producer may take the maximum of the two profile endpoints. -/
theorem convexOn_sparseUpperFourthOrderNormalizedMajorant
    {lambda frequency : ℝ} (hlambda : lambda < 1) :
    ConvexOn ℝ (Set.Ici 0)
      (fun profile ↦ sparseUpperFourthOrderNormalizedMajorant
        profile lambda frequency) := by
  let s : ℂ := lambda + frequency * Complex.I
  let A : ℂ := (1 - s) ^ (-1 / 2 : ℂ)
  let B : ℂ := s ^ 2 * (1 - s) ^ (-5 / 2 : ℂ)
  let d8 := quadraticExpDerivativeMajorant 8 ‖s‖ lambda
  let d6 := quadraticExpDerivativeMajorant 6 ‖s‖ lambda
  have hd8 : 0 ≤ d8 := quadraticExpDerivativeMajorant_nonneg (norm_nonneg s) hlambda
  have hd6 : 0 ≤ d6 := quadraticExpDerivativeMajorant_nonneg (norm_nonneg s) hlambda
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hlead : ‖A - (((a * x + b * y) / 8 : ℝ) : ℂ) * B‖ ≤
      a * ‖A - (((x / 8 : ℝ) : ℂ) * B)‖ +
        b * ‖A - (((y / 8 : ℝ) : ℂ) * B)‖ := by
    have hdecomp :
        A - (((a * x + b * y) / 8 : ℝ) : ℂ) * B =
          (a : ℂ) * (A - (((x / 8 : ℝ) : ℂ) * B)) +
            (b : ℂ) * (A - (((y / 8 : ℝ) : ℂ) * B)) := by
      push_cast
      have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      nth_rewrite 1 [← one_mul A]
      rw [← habC]
      ring
    rw [hdecomp]
    calc
      _ ≤ ‖(a : ℂ) * (A - (((x / 8 : ℝ) : ℂ) * B))‖ +
          ‖(b : ℂ) * (A - (((y / 8 : ℝ) : ℂ) * B))‖ := norm_add_le _ _
      _ = _ := by simp [abs_of_nonneg ha, abs_of_nonneg hb]
  have hsq := (convexOn_pow (𝕜 := ℝ) 2).2 hx hy ha hb hab
  have hrpow := (convexOn_rpow (p := (3 / 2 : ℝ)) (by norm_num)).2
    hx hy ha hb hab
  simp only [smul_eq_mul] at hsq hrpow ⊢
  simp only [sparseUpperFourthOrderNormalizedMajorant]
  have hcombo : 0 ≤ a * x + b * y :=
    add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  rw [mul_sqrt_eq_rpow_three_halves hcombo,
    mul_sqrt_eq_rpow_three_halves hx,
    mul_sqrt_eq_rpow_three_halves hy]
  dsimp only [A, B, s, d8, d6] at hlead hd8 hd6
  have hsqrt : 0 ≤ Real.sqrt (1 - lambda) := Real.sqrt_nonneg _
  let g : ℝ → ℝ := fun p ↦
    ‖(1 - ((lambda : ℂ) + (frequency : ℂ) * Complex.I)) ^ (-1 / 2 : ℂ) -
        ((p / 8 : ℝ) : ℂ) *
          ((lambda : ℂ) + (frequency : ℂ) * Complex.I) ^ 2 *
          (1 - ((lambda : ℂ) + (frequency : ℂ) * Complex.I)) ^ (-5 / 2 : ℂ)‖
  have hg : g (a * x + b * y) ≤ a * g x + b * g y := by
    dsimp only [g]
    simpa only [mul_assoc] using hlead
  let f : ℝ → ℝ := fun p ↦
    g p +
      p ^ 2 / 9216 * quadraticExpDerivativeMajorant 8
        ‖(lambda : ℂ) + (frequency : ℂ) * Complex.I‖ lambda +
      11 * p ^ (3 / 2 : ℝ) / 5760 * quadraticExpDerivativeMajorant 6
        ‖(lambda : ℂ) + (frequency : ℂ) * Complex.I‖ lambda
  change Real.sqrt (1 - lambda) * f (a * x + b * y) ≤
    a * (Real.sqrt (1 - lambda) * f x) +
      b * (Real.sqrt (1 - lambda) * f y)
  have hsqTerm :
      (a * x + b * y) ^ 2 / 9216 *
          quadraticExpDerivativeMajorant 8
            ‖(lambda : ℂ) + (frequency : ℂ) * Complex.I‖ lambda ≤
        (a * x ^ 2 + b * y ^ 2) / 9216 *
          quadraticExpDerivativeMajorant 8
            ‖(lambda : ℂ) + (frequency : ℂ) * Complex.I‖ lambda := by
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hsq (by norm_num)) hd8
  have hrpowTerm :
      11 * (a * x + b * y) ^ (3 / 2 : ℝ) / 5760 *
          quadraticExpDerivativeMajorant 6
            ‖(lambda : ℂ) + (frequency : ℂ) * Complex.I‖ lambda ≤
        11 * (a * x ^ (3 / 2 : ℝ) + b * y ^ (3 / 2 : ℝ)) / 5760 *
          quadraticExpDerivativeMajorant 6
            ‖(lambda : ℂ) + (frequency : ℂ) * Complex.I‖ lambda := by
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow (by norm_num)) (by norm_num)) hd6
  have hf : f (a * x + b * y) ≤ a * f x + b * f y := by
    dsimp only [f]
    nlinarith [hg, hsqTerm, hrpowTerm]
  calc
    _ ≤ Real.sqrt (1 - lambda) * (a * f x + b * f y) :=
      mul_le_mul_of_nonneg_left hf hsqrt
    _ = _ := by ring

/-- The real row endpoint selected by one executable Gaussian cell. -/
noncomputable def gaussianCellRowUpperValue
    (profileLeft profileRight lam mesh : ℚ) (index : ℕ) : ℝ :=
  let frequencyLeft := index * mesh
  let frequencyRight := (index + 1) * mesh
  let expressionLeft :=
    rowExpressionOnCell profileLeft frequencyLeft frequencyRight lam
  let expressionRight :=
    rowExpressionOnCell profileRight frequencyLeft frequencyRight lam
  let cap := realCapUpper contourPrecision profileLeft lam
  Dyadic.toReal contourPrecision
    (min cap.hi (max expressionLeft.hi expressionRight.hi))

/-- The row value selected by a generated cell majorizes the actual canonical
U4/U8 minimum throughout both its profile and frequency intervals. -/
theorem sparseUpperContourRowMajorant_le_gaussianCellRowUpperValue
    (profileLeft profileRight lam mesh : ℚ) (index : ℕ)
    (profile frequency : ℝ)
    (hprofileLeftNonneg : (0 : ℝ) ≤ profileLeft)
    (hprofile : profile ∈ Set.Icc (profileLeft : ℝ) (profileRight : ℝ))
    (hlam : (lam : ℝ) < 1)
    (hleft :
      (rowExpressionOnCell profileLeft (index * mesh) ((index + 1) * mesh) lam).Contains
        (UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
          profileLeft lam frequency))
    (hright :
      (rowExpressionOnCell profileRight (index * mesh) ((index + 1) * mesh) lam).Contains
        (UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
          profileRight lam frequency))
    (hcap : (realCapUpper contourPrecision profileLeft lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ))))) :
    sparseUpperContourRowMajorant profile (lam : ℝ) frequency ≤
      gaussianCellRowUpperValue profileLeft profileRight lam mesh index := by
  have hleftCanonical :
      sparseUpperFourthOrderNormalizedMajorant
          (profileLeft : ℝ) (lam : ℝ) frequency ≤
        Dyadic.toReal contourPrecision
          (rowExpressionOnCell profileLeft (index * mesh)
            ((index + 1) * mesh) lam).hi := by
    rw [← normalizedFourthOrderRowBound_eq_sparseUpperMajorant
      profileLeft lam frequency hlam]
    exact hleft.2
  have hrightCanonical :
      sparseUpperFourthOrderNormalizedMajorant
          (profileRight : ℝ) (lam : ℝ) frequency ≤
        Dyadic.toReal contourPrecision
          (rowExpressionOnCell profileRight (index * mesh)
            ((index + 1) * mesh) lam).hi := by
    rw [← normalizedFourthOrderRowBound_eq_sparseUpperMajorant
      profileRight lam frequency hlam]
    exact hright.2
  have hconvex :=
    (convexOn_sparseUpperFourthOrderNormalizedMajorant
      (frequency := frequency) hlam).le_max_of_mem_Icc
      (show (profileLeft : ℝ) ∈ Set.Ici 0 by exact hprofileLeftNonneg)
      (show (profileRight : ℝ) ∈ Set.Ici 0 by
        exact hprofileLeftNonneg.trans (hprofile.1.trans hprofile.2))
      hprofile
  have hU4 : sparseUpperFourthOrderNormalizedMajorant profile (lam : ℝ) frequency ≤
      Dyadic.toReal contourPrecision
        (max
          (rowExpressionOnCell profileLeft (index * mesh) ((index + 1) * mesh) lam).hi
          (rowExpressionOnCell profileRight (index * mesh) ((index + 1) * mesh) lam).hi) := by
    rw [toReal_max]
    exact hconvex.trans (max_le_max hleftCanonical hrightCanonical)
  have hU8 : realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ))) ≤
      Dyadic.toReal contourPrecision (realCapUpper contourPrecision profileLeft lam).hi :=
    hcap.2
  rw [sparseUpperContourRowMajorant, gaussianCellRowUpperValue, toReal_min]
  simpa only [min_comm] using min_le_min hU4 hU8

theorem sparseUpperContourRowMajorant_nonneg
    {profile lambda frequency : ℝ} (hprofile : 0 ≤ profile)
    (hlambda : 0 ≤ lambda) (hlambdaOne : lambda < 1) :
    0 ≤ sparseUpperContourRowMajorant profile lambda frequency := by
  apply le_min
  · unfold sparseUpperFourthOrderNormalizedMajorant
    have hd8 := quadraticExpDerivativeMajorant_nonneg (m := 8)
      (norm_nonneg (lambda + frequency * Complex.I)) hlambdaOne
    have hd6 := quadraticExpDerivativeMajorant_nonneg (m := 6)
      (norm_nonneg (lambda + frequency * Complex.I)) hlambdaOne
    have hsqrtProfile : 0 ≤ Real.sqrt profile := Real.sqrt_nonneg _
    positivity
  · exact Internal.realRowDeficitCap_nonneg (by positivity)

end SparseUpperContour
end CertifiedJL
