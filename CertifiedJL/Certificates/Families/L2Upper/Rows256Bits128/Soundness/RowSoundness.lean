/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Core
import CertifiedJL.Certificates.Shared.UpperContourSoundness
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContour
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperRealDeficit

/-!
# Live sparse row soundness for the centered-hybrid certificate

This file contains exactly the real-axis cap, fourth-order convexity, and
nonnegativity facts consumed by the hybrid proof.  It deliberately excludes
the retired ten-box Gaussian quadrature certificate.
-/

namespace CertifiedJL
namespace SparseUpperHybrid

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

private theorem toReal_mono {p : ℕ} {a b : ℤ} (h : a ≤ b) :
    Dyadic.toReal p a ≤ Dyadic.toReal p b := by
  unfold Dyadic.toReal
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

private theorem toReal_scale (p : ℕ) :
    Dyadic.toReal p (Dyadic.scale p : ℤ) = 1 := by
  simp [Dyadic.toReal]

private theorem toReal_min (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (min a b) = min (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (toReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (toReal_mono h')]

private theorem toReal_max (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (max a b) = max (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (toReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (toReal_mono h')]

private theorem contains_foldl_add
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

private theorem foldl_add_eq_add_sum_map
    {A : Type*} (xs : List A) (f : A → ℝ) (x : ℝ) :
    xs.foldl (fun acc i ↦ acc + f i) x = x + (xs.map f).sum := by
  induction xs generalizing x with
  | nil => simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring

private theorem finset_sum_range_eq_list_sum_map
    (n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, List.range_succ, ih]

private theorem sum_map_sum_eq_sum_flatMap
    {A B : Type*} (xs : List A) (g : A → List B) (f : B → ℝ) :
    (xs.map (fun x ↦ ((g x).map f).sum)).sum =
      ((xs.flatMap g).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.sum_append]

private theorem realRowDeficitCap_nonneg {v : ℝ} (hv : 0 ≤ v) :
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
        · simpa [toReal_scale] using toReal_mono (p := p) horder
      · have horder' : result.hi ≤ (Dyadic.scale p : ℤ) :=
          le_of_not_ge horder
        rw [min_eq_right horder', min_eq_right]
        simpa [toReal_scale] using toReal_mono (p := p) horder'
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
    exact realRowDeficitCap_nonneg
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlamReal) hdenominatorReal)
  · exact hu

/-- The literal real value evaluated by the independent high-profile
certificate, including the `2^128` scaling used by its strict endpoint check. -/
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
  · exact realRowDeficitCap_nonneg (by positivity)

/-- Gaussian-decayed sparse row integrand used only as the integrable
dominator for the centered-hybrid integrand. -/
noncomputable def gaussianSparseRowIntegrand
    (lam sigma : ℚ) (profile frequency : ℝ) : ℝ :=
  Real.exp (-((sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
    sparseUpperContourRowMajorant profile (lam : ℝ) frequency ^ rows *
    (1 / Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2))

theorem continuous_gaussianSparseRowIntegrand
    (lam sigma : ℚ) (profile : ℝ) (hlam : 0 < (lam : ℝ))
    (hlamOne : (lam : ℝ) < 1) :
    Continuous (gaussianSparseRowIntegrand lam sigma profile) := by
  have hbase : Continuous (fun frequency : ℝ =>
      (1 : ℂ) - ((lam : ℂ) + (frequency : ℂ) * Complex.I)) := by
    fun_prop
  have hslit : ∀ frequency : ℝ,
      (1 : ℂ) - ((lam : ℂ) + (frequency : ℂ) * Complex.I) ∈
        Complex.slitPlane := by
    intro frequency
    rw [Complex.mem_slitPlane_iff]
    left
    simp
    linarith
  have hpowOne : Continuous (fun frequency : ℝ =>
      ((1 : ℂ) - ((lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
        (-1 / 2 : ℂ)) :=
    hbase.cpow continuous_const hslit
  have hpowFive : Continuous (fun frequency : ℝ =>
      ((1 : ℂ) - ((lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
        (-5 / 2 : ℂ)) :=
    hbase.cpow continuous_const hslit
  have hs : Continuous (fun frequency : ℝ =>
      (lam : ℂ) + (frequency : ℂ) * Complex.I) := by fun_prop
  have hleading : Continuous (fun frequency : ℝ =>
      ‖((1 : ℂ) - ((lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
          (-1 / 2 : ℂ) -
        ((profile / 8 : ℝ) : ℂ) *
          ((lam : ℂ) + (frequency : ℂ) * Complex.I) ^ 2 *
        ((1 : ℂ) - ((lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
          (-5 / 2 : ℂ)‖) := by
    simpa only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, mul_assoc] using
      (hpowOne.sub
        ((continuous_const : Continuous fun _ : ℝ => ((profile / 8 : ℝ) : ℂ)).mul
          ((hs.pow 2).mul hpowFive))).norm
  have hd8 : Continuous (fun frequency : ℝ =>
      quadraticExpDerivativeMajorant 8
        ‖(lam : ℂ) + (frequency : ℂ) * Complex.I‖ (lam : ℝ)) := by
    unfold quadraticExpDerivativeMajorant
    fun_prop
  have hd6 : Continuous (fun frequency : ℝ =>
      quadraticExpDerivativeMajorant 6
        ‖(lam : ℂ) + (frequency : ℂ) * Complex.I‖ (lam : ℝ)) := by
    unfold quadraticExpDerivativeMajorant
    fun_prop
  have hU4 : Continuous (fun frequency : ℝ =>
      sparseUpperFourthOrderNormalizedMajorant profile (lam : ℝ) frequency) := by
    unfold sparseUpperFourthOrderNormalizedMajorant
    exact continuous_const.mul
      ((hleading.add (continuous_const.mul hd8)).add (continuous_const.mul hd6))
  have hrow : Continuous (fun frequency : ℝ =>
      sparseUpperContourRowMajorant profile (lam : ℝ) frequency) := by
    unfold sparseUpperContourRowMajorant
    exact hU4.min continuous_const
  have hsqrt : Continuous (fun frequency : ℝ =>
      Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2)) := by fun_prop
  have hsqrtNe : ∀ frequency : ℝ,
      Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2) ≠ 0 := by
    intro frequency
    positivity
  have hinverse : Continuous (fun frequency : ℝ =>
      1 / Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2)) := by
    exact continuous_const.div₀ hsqrt hsqrtNe
  unfold gaussianSparseRowIntegrand
  exact ((by fun_prop : Continuous (fun frequency : ℝ =>
      Real.exp (-((sigma : ℝ) ^ 2 / 2) * frequency ^ 2))).mul
        (hrow.pow rows)).mul hinverse

theorem integrable_gaussianSparseRowIntegrand
    (lam sigma : ℚ) (profile : ℝ) (hprofile : 0 ≤ profile)
    (hlam : 0 < (lam : ℝ)) (hlamOne : (lam : ℝ) < 1)
    (hsigma : 0 < (sigma : ℝ)) :
    Integrable (gaussianSparseRowIntegrand lam sigma profile) := by
  let cap := realRowDeficitCap
    (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ)))
  let dominating : ℝ → ℝ := fun frequency =>
    (cap ^ rows / (lam : ℝ)) *
      Real.exp (-((sigma : ℝ) ^ 2 / 2) * frequency ^ 2)
  have hdominating : Integrable dominating := by
    exact (integrable_exp_neg_mul_sq
      (by positivity : 0 < (sigma : ℝ) ^ 2 / 2)).const_mul _
  apply hdominating.mono'
    (continuous_gaussianSparseRowIntegrand lam sigma profile hlam hlamOne).aestronglyMeasurable
  filter_upwards [] with frequency
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · have hrowNonneg := sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne
    have hrowCap : sparseUpperContourRowMajorant profile (lam : ℝ) frequency ≤
        cap := min_le_right _ _
    have hpower := pow_le_pow_left₀ hrowNonneg hrowCap rows
    have hsqrt : (lam : ℝ) ≤
        Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2) := by
      exact (Real.le_sqrt hlam.le (by positivity)).2
        (by nlinarith [sq_nonneg frequency])
    have hinverse : 1 / Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2) ≤
        1 / (lam : ℝ) := one_div_le_one_div_of_le hlam hsqrt
    have hcapNonneg : 0 ≤ cap := realRowDeficitCap_nonneg (by positivity)
    unfold gaussianSparseRowIntegrand dominating
    dsimp only [cap]
    calc
      _ ≤ Real.exp (-((sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          cap ^ rows * (1 / (lam : ℝ)) := by gcongr
      _ = _ := by ring
  · unfold gaussianSparseRowIntegrand
    positivity [sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne]

end SparseUpperHybrid
end CertifiedJL
