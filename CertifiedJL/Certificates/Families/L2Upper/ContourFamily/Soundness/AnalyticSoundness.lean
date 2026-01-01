/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Soundness
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.AnalyticCore
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoFinal

/-!
# Generic analytic soundness for parameterized balanced-ternary contours

This module connects the executable family kernel to the analytic contour.
It separates two kinds of evidence:

* reusable analytic facts, proved once for arbitrary factored row/security
  parameters; and
* local segmented-quadrature enclosures, which generated instances discharge
  by kernel replay.

The resulting constructors produce `LowProfileBoxSound` and
`HighProfileBoxSound` directly.  No Boolean result is treated as an analytic
fact: interval containment and integral domination remain explicit Lean
propositions.
-/

open scoped ENNReal BigOperators

namespace CertifiedJL.SparseUpperContourFamily

open MeasureTheory ProbabilityTheory Set

/-- The family row coefficients denote the established balanced-ternary
fourth-order majorant. -/
theorem normalizedFourthOrderRowBound_eq_sparseUpperMajorant
    (profile lambda : ℚ) (frequency : ℝ) (hlambda : (lambda : ℝ) < 1) :
    UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
        profile lambda frequency =
      sparseUpperFourthOrderNormalizedMajorant
        (profile : ℝ) (lambda : ℝ) frequency := by
  simpa [rowCoefficients, SparseUpperContour.rowCoefficients] using
    SparseUpperContour.normalizedFourthOrderRowBound_eq_sparseUpperMajorant
      profile lambda frequency hlambda

/-- Generic bridge from the shared real-cap proof to the family spelling of
the identical executable cap. -/
theorem contains_realCapUpper_of_ne_zero
    (precision : ℕ) (profileLeft lam : ℚ) (profile : ℝ)
    (hprofileLeft : 0 ≤ profileLeft) (hprofileLeftNe : profileLeft ≠ 0)
    (hprofile : (profileLeft : ℝ) ≤ profile)
    (hlam : 0 ≤ lam) (hlamOne : lam < 1)
    (hsqrtInput : 0 ≤ (UpperContourKernel.frac precision profileLeft).lo)
    (hexponentUpper :
      let squareRootLower :=
        (UpperContourKernel.frac precision profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      exponent < (2 ^ 30 : ℕ))
    (hexponentBase :
      let squareRootLower :=
        (UpperContourKernel.frac precision profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      0 < (Interval.ofRat precision (1 - exponent / (2 ^ 30 : ℕ))).lo)
    (hdenominatorInput :
      let squareRootLower :=
        (UpperContourKernel.frac precision profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 ≤ (UpperContourKernel.frac precision (1 + argument)).lo)
    (hdenominator :
      let squareRootLower :=
        (UpperContourKernel.frac precision profileLeft).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 < (UpperContourKernel.frac precision 2 *
        (UpperContourKernel.frac precision (1 + argument)).sqrt).lo) :
    (realCapUpper precision profileLeft lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ)))) := by
  simpa only [realCapUpper, SparseUpperContour.realCapUpper] using
    SparseUpperContour.contains_realCapUpper_of_ne_zero precision profileLeft
      lam profile hprofileLeft hprofileLeftNe hprofile hlam hlamOne hsqrtInput
      hexponentUpper hexponentBase hdenominatorInput hdenominator

/-- The zero-left profile box uses the unit cap. The same executable side
conditions as the nonzero constructor certify its upper endpoint. -/
theorem contains_realCapUpper_of_eq_zero
    (precision : ℕ) (lam : ℚ) (profile : ℝ)
    (hprofile : 0 ≤ profile) (hlam : 0 ≤ lam) (hlamOne : lam < 1)
    (hsqrtInput : 0 ≤ (UpperContourKernel.frac precision 0).lo)
    (hexponentUpper :
      let squareRootLower :=
        (UpperContourKernel.frac precision 0).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      exponent < (2 ^ 30 : ℕ))
    (hexponentBase :
      let squareRootLower :=
        (UpperContourKernel.frac precision 0).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      let exponent := argument / (1 + argument)
      0 < (Interval.ofRat precision
        (1 - exponent / (2 ^ 30 : ℕ))).lo)
    (hdenominatorInput :
      let squareRootLower :=
        (UpperContourKernel.frac precision 0).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 ≤ (UpperContourKernel.frac precision (1 + argument)).lo)
    (hdenominator :
      let squareRootLower :=
        (UpperContourKernel.frac precision 0).sqrt.lowerRat
      let argument := squareRootLower * lam / (1 - lam)
      0 < (UpperContourKernel.frac precision 2 *
        (UpperContourKernel.frac precision (1 + argument)).sqrt).lo) :
    (realCapUpper precision 0 lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ)))) := by
  have hu := SparseUpperContour.upperBounds_realCapUpper precision 0 lam
    profile (by norm_num) (by simpa using hprofile) hlam hlamOne hsqrtInput hexponentUpper
      hexponentBase hdenominatorInput hdenominator
  constructor
  · rw [realCapUpper, if_pos rfl]
    simp only [Dyadic.toReal_zero]
    unfold realRowDeficitCap
    positivity
  · simpa only [realCapUpper, SparseUpperContour.realCapUpper] using hu

/-- Literal integrand under the positive-frequency shifted-Gaussian contour. -/
noncomputable def actualBoxQuadratureIntegrand
    (parameters : Parameters) (box : ProfileBox)
    (profile frequency : ℝ) : ℝ :=
  Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^
      parameters.rows *
    (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))

/-- Literal rational prefactor represented by `boxPrefactor`. -/
noncomputable def boxRationalPrefactorValue
    (parameters : Parameters) (box : ProfileBox) : ℝ :=
  let exponent := box.lam *
      (parameters.threshold - box.theta * box.sigma) -
    box.sigma * box.sigma * box.lam * box.lam / 2
  (2 ^ parameters.securityBits : ℝ) *
    (((1 / (314159 / 100000) : ℚ) : ℝ)) *
    (((1 / UpperContourKernel.phiLower box.theta : ℚ) : ℝ)) *
    Real.exp (-(exponent : ℚ)) *
    (((1 / (1 - box.lam) ^ (parameters.rows / 2) : ℚ) : ℝ))

/-- Literal prefactor in the analytic shifted-Gaussian inequality. -/
noncomputable def boxActualPrefactorValue
    (parameters : Parameters) (box : ProfileBox) : ℝ :=
  let exponent := box.lam *
      (parameters.threshold - box.theta * box.sigma) -
    box.sigma * box.sigma * box.lam * box.lam / 2
  (2 ^ parameters.securityBits : ℝ) * (1 / Real.pi) *
    (1 / standardGaussianCDF (box.theta : ℝ)) *
    Real.exp (-(exponent : ℚ)) *
    (((1 / (1 - box.lam) ^ (parameters.rows / 2) : ℚ) : ℝ))

/-- Analytic and elementary side conditions shared by one low-profile box. -/
structure LowProfileFacts (parameters : Parameters) (box : ProfileBox) : Prop where
  profileLeft_nonneg : 0 ≤ box.profileLeft
  profileLeft_le_right : box.profileLeft ≤ box.profileRight
  theta_nonneg : 0 ≤ box.theta
  theta_le : box.theta ≤ 1
  phi_pos : 0 < UpperContourKernel.phiLower box.theta
  lam_pos : 0 < box.lam
  lam_lt_one : box.lam < 1
  sigma_pos : 0 < box.sigma
  exponent_nonneg :
    0 ≤ box.lam * (parameters.threshold - box.theta * box.sigma) -
      box.sigma * box.sigma * box.lam * box.lam / 2
  rows_even : Even parameters.rows

/-- Analytic side conditions for the independent high-profile endpoint. -/
structure HighProfileFacts
    (parameters : Parameters) (box : HighProfileBox) : Prop where
  profileMinimum_nonneg : 0 ≤ box.profileMinimum
  lam_nonneg : 0 ≤ box.lam
  lam_lt_one : box.lam < 1
  exponent_nonneg : 0 ≤ box.lam * parameters.threshold
  rows_even : Even parameters.rows
  capContains : ∀ profile : ℝ,
    (box.profileMinimum : ℝ) ≤ profile →
    (realCapUpper parameters.precision box.profileMinimum box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) /
          (1 - (box.lam : ℝ))))

/-- The square-root normalization raised to an even row count is the rational
half-power used by the executable prefactors. -/
theorem inverseSqrtPow_eq_halfPower
    {rows : ℕ} (hrows : Even rows) {lam : ℝ} (hlam : lam < 1) :
    (1 / Real.sqrt (1 - lam)) ^ rows =
      (1 / (1 - lam)) ^ (rows / 2) := by
  obtain ⟨half, hrowsEq⟩ := hrows
  have hsqrtSq : Real.sqrt (1 - lam) ^ 2 = 1 - lam :=
    Real.sq_sqrt (sub_nonneg.mpr hlam.le)
  have hinvSq :
      (1 / Real.sqrt (1 - lam)) ^ 2 = 1 / (1 - lam) := by
    rw [div_pow, one_pow, hsqrtSq]
  subst rows
  have hhalf : (half + half) / 2 = half := by omega
  rw [hhalf, show half + half = 2 * half by omega, pow_mul, hinvSq]

/-- The executable low-profile prefactor contains its literal rational value. -/
theorem boxPrefactor_contains_rationalValue
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box) :
    (boxPrefactor parameters box).Contains
      (boxRationalPrefactorValue parameters box) := by
  have hscaledExponential := UpperContourKernel.scaledNegExpUpper_contains
    parameters.precision parameters.securityBlockBits
      (box.lam * (parameters.threshold - box.theta * box.sigma) -
        box.sigma * box.sigma * box.lam * box.lam / 2)
      32 parameters.securityScaleSquarings facts.exponent_nonneg
  have hpi := Interval.contains_ofRat parameters.precision
    (1 / (314159 / 100000) : ℚ)
  have hphi := Interval.contains_ofRat parameters.precision
    (1 / UpperContourKernel.phiLower box.theta : ℚ)
  have hgaussian := Interval.contains_ofRat parameters.precision
    (1 / (1 - box.lam) ^ (parameters.rows / 2) : ℚ)
  have hproduct := Interval.contains_mul
    (Interval.contains_mul
      (Interval.contains_mul hscaledExponential hpi) hphi) hgaussian
  simpa [boxPrefactor, boxRationalPrefactorValue, Parameters.securityBits,
    UpperContourKernel.frac, mul_assoc, mul_left_comm, mul_comm] using hproduct

/-- The rational reciprocal factors majorize the true `pi` and Gaussian-CDF
reciprocals. -/
theorem boxActualPrefactorValue_le_rationalValue
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box) :
    boxActualPrefactorValue parameters box ≤
      boxRationalPrefactorValue parameters box := by
  have hpiPos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpiLowerPos : (0 : ℝ) < 314159 / 100000 := by norm_num
  have hpiInv : 1 / Real.pi ≤ (((1 / (314159 / 100000) : ℚ) : ℝ)) := by
    norm_num only [one_div, Rat.cast_inv, Rat.cast_ofScientific,
      Rat.cast_natCast]
    rw [show (100000 : ℝ) / 314159 =
      ((314159 : ℝ) / 100000)⁻¹ by norm_num]
    exact (inv_le_inv₀ hpiPos hpiLowerPos).2
      SparseUpperContour.piLower_lt_pi.le
  have hphiReal : (0 : ℝ) <
      ((UpperContourKernel.phiLower box.theta : ℚ) : ℝ) := by
    exact_mod_cast facts.phi_pos
  have hCDFPos : 0 < standardGaussianCDF (box.theta : ℝ) :=
    standardGaussianCDF_pos _
  have hphiLe :
      ((UpperContourKernel.phiLower box.theta : ℚ) : ℝ) ≤
        standardGaussianCDF (box.theta : ℝ) :=
    SparseUpperContour.phiLower_le_standardGaussianCDF_of_le_one box.theta
      facts.theta_nonneg facts.theta_le
  have hphiInv : 1 / standardGaussianCDF (box.theta : ℝ) ≤
      (((1 / UpperContourKernel.phiLower box.theta : ℚ) : ℝ)) := by
    norm_num only [one_div, Rat.cast_inv]
    exact (inv_le_inv₀ hCDFPos hphiReal).2 hphiLe
  have hgaussian : (0 : ℝ) ≤
      (((1 / (1 - box.lam) ^ (parameters.rows / 2) : ℚ) : ℝ)) := by
    have hlamDiff : (0 : ℚ) < 1 - box.lam := sub_pos.mpr facts.lam_lt_one
    positivity
  unfold boxActualPrefactorValue boxRationalPrefactorValue
  dsimp only
  gcongr

/-- The generic positive-frequency integrand is pointwise nonnegative. -/
theorem actualBoxQuadratureIntegrand_nonneg
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile) (frequency : ℝ) :
    0 ≤ actualBoxQuadratureIntegrand parameters box profile frequency := by
  unfold actualBoxQuadratureIntegrand
  have hlam0 : (0 : ℝ) ≤ box.lam := by
    exact_mod_cast facts.lam_pos.le
  have hlam1 : (box.lam : ℝ) < 1 := by
    exact_mod_cast facts.lam_lt_one
  positivity [SparseUpperContour.sparseUpperContourRowMajorant_nonneg
    (frequency := frequency) hprofile hlam0 hlam1]

/-- The generic positive-frequency integrand is integrable for every valid
low-profile box. -/
theorem integrable_actualBoxQuadratureIntegrand
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile) :
    Integrable (actualBoxQuadratureIntegrand parameters box profile) := by
  let cap := realRowDeficitCap
    (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))
  let dominating : ℝ → ℝ := fun frequency ↦
    (cap ^ parameters.rows / (box.lam : ℝ)) *
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2)
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast facts.lam_pos
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast facts.lam_lt_one
  have hsigma : 0 < (box.sigma : ℝ) := by exact_mod_cast facts.sigma_pos
  have hdominating : Integrable dominating := by
    exact (integrable_exp_neg_mul_sq
      (by positivity : 0 < (box.sigma : ℝ) ^ 2 / 2)).const_mul _
  have hmeasurable :
      AEStronglyMeasurable
        (actualBoxQuadratureIntegrand parameters box profile) := by
    apply Measurable.aestronglyMeasurable
    unfold actualBoxQuadratureIntegrand sparseUpperContourRowMajorant
      sparseUpperFourthOrderNormalizedMajorant realRowDeficitCap
      quadraticExpDerivativeMajorant
    fun_prop
  apply hdominating.mono' hmeasurable
  filter_upwards [] with frequency
  rw [Real.norm_eq_abs, abs_of_nonneg
    (actualBoxQuadratureIntegrand_nonneg facts hprofile frequency)]
  have hrowNonneg := SparseUpperContour.sparseUpperContourRowMajorant_nonneg
    (frequency := frequency) hprofile hlam.le hlamOne
  have hrowCap :
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤ cap :=
    min_le_right _ _
  have hpower := pow_le_pow_left₀ hrowNonneg hrowCap parameters.rows
  have hsqrt : (box.lam : ℝ) ≤
      Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) :=
    (Real.le_sqrt hlam.le (by positivity)).2 (by nlinarith [sq_nonneg frequency])
  have hinverse :
      1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) ≤
        1 / (box.lam : ℝ) :=
    one_div_le_one_div_of_le hlam hsqrt
  have hcapNonneg : 0 ≤ cap := by
    dsimp only [cap]
    unfold realRowDeficitCap
    positivity
  unfold actualBoxQuadratureIntegrand
  dsimp only [dominating, cap]
  calc
    _ ≤ Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
        realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) /
            (1 - (box.lam : ℝ))) ^ parameters.rows *
        (1 / (box.lam : ℝ)) := by gcongr
    _ = _ := by ring

private theorem dyadicToReal_mono {precision : ℕ} {a b : ℤ} (h : a ≤ b) :
    Dyadic.toReal precision a ≤ Dyadic.toReal precision b := by
  unfold Dyadic.toReal
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

private theorem dyadic_nonneg_of_toReal_nonneg
    {precision : ℕ} {a : ℤ} (h : 0 ≤ Dyadic.toReal precision a) : 0 ≤ a := by
  unfold Dyadic.toReal at h
  rcases (div_nonneg_iff.mp h) with hpositive | hnegative
  · exact_mod_cast hpositive.1
  · have hscale : (0 : ℝ) < Dyadic.scale precision := by
      exact_mod_cast Dyadic.scale_pos precision
    exact (not_lt_of_ge hnegative.2 hscale).elim

private theorem dyadicToReal_min (precision : ℕ) (a b : ℤ) :
    Dyadic.toReal precision (min a b) =
      min (Dyadic.toReal precision a) (Dyadic.toReal precision b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (dyadicToReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (dyadicToReal_mono h')]

private theorem dyadicToReal_max (precision : ℕ) (a b : ℤ) :
    Dyadic.toReal precision (max a b) =
      max (Dyadic.toReal precision a) (Dyadic.toReal precision b) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (dyadicToReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (dyadicToReal_mono h')]

private theorem finset_sum_range_eq_list_sum_map
    (count : ℕ) (f : ℕ → ℝ) :
    ∑ index ∈ Finset.range count, f index =
      ((List.range count).map f).sum := by
  induction count with
  | zero => simp
  | succ count ih => simp [Finset.sum_range_succ, List.range_succ, ih]

/-- Literal row endpoint selected by one executable segmented cell. -/
noncomputable def gaussianCellRowUpperValue
    (parameters : Parameters) (box : ProfileBox)
    (segment : Segment) (index : ℕ) : ℝ :=
  Dyadic.toReal parameters.precision <|
    min (realCapUpper parameters.precision box.profileLeft box.lam).hi
      (max
        (rowExpressionOnCell parameters box.profileLeft
          (segment.cellLeft index) (segment.cellRight index) box.lam).hi
        (rowExpressionOnCell parameters box.profileRight
          (segment.cellLeft index) (segment.cellRight index) box.lam).hi)

/-- Family-facing form of convexity in the nonnegative profile parameter. -/
theorem convexOn_sparseUpperFourthOrderNormalizedMajorant
    {lambda frequency : ℝ} (hlambda : lambda < 1) :
    ConvexOn ℝ (Ici 0)
      (fun profile ↦ sparseUpperFourthOrderNormalizedMajorant
        profile lambda frequency) :=
  SparseUpperContour.convexOn_sparseUpperFourthOrderNormalizedMajorant hlambda

/-- Two checked profile-endpoint expressions and one real-cap enclosure
majorize the canonical row minimum throughout a segmented profile/frequency
cell. -/
theorem sparseUpperContourRowMajorant_le_gaussianCellRowUpperValue
    (parameters : Parameters) (box : ProfileBox)
    (segment : Segment) (index : ℕ)
    (profile frequency : ℝ)
    (hprofileLeftNonneg : (0 : ℝ) ≤ box.profileLeft)
    (hprofile : profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ))
    (hlam : (box.lam : ℝ) < 1)
    (hleft :
      (rowExpressionOnCell parameters box.profileLeft
        (segment.cellLeft index) (segment.cellRight index) box.lam).Contains
        (UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
          box.profileLeft box.lam frequency))
    (hright :
      (rowExpressionOnCell parameters box.profileRight
        (segment.cellLeft index) (segment.cellRight index) box.lam).Contains
        (UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
          box.profileRight box.lam frequency))
    (hcap : (realCapUpper parameters.precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      gaussianCellRowUpperValue parameters box segment index := by
  have hleftCanonical :
      sparseUpperFourthOrderNormalizedMajorant
          (box.profileLeft : ℝ) (box.lam : ℝ) frequency ≤
        Dyadic.toReal parameters.precision
          (rowExpressionOnCell parameters box.profileLeft
            (segment.cellLeft index) (segment.cellRight index) box.lam).hi := by
    rw [← normalizedFourthOrderRowBound_eq_sparseUpperMajorant
      box.profileLeft box.lam frequency hlam]
    exact hleft.2
  have hrightCanonical :
      sparseUpperFourthOrderNormalizedMajorant
          (box.profileRight : ℝ) (box.lam : ℝ) frequency ≤
        Dyadic.toReal parameters.precision
          (rowExpressionOnCell parameters box.profileRight
            (segment.cellLeft index) (segment.cellRight index) box.lam).hi := by
    rw [← normalizedFourthOrderRowBound_eq_sparseUpperMajorant
      box.profileRight box.lam frequency hlam]
    exact hright.2
  have hconvex :=
    (convexOn_sparseUpperFourthOrderNormalizedMajorant
      (frequency := frequency) hlam).le_max_of_mem_Icc
      (show (box.profileLeft : ℝ) ∈ Ici 0 by exact hprofileLeftNonneg)
      (show (box.profileRight : ℝ) ∈ Ici 0 by
        exact hprofileLeftNonneg.trans (hprofile.1.trans hprofile.2))
      hprofile
  have hfourth :
      sparseUpperFourthOrderNormalizedMajorant
          profile (box.lam : ℝ) frequency ≤
        Dyadic.toReal parameters.precision
          (max
            (rowExpressionOnCell parameters box.profileLeft
              (segment.cellLeft index) (segment.cellRight index) box.lam).hi
            (rowExpressionOnCell parameters box.profileRight
              (segment.cellLeft index) (segment.cellRight index) box.lam).hi) := by
    rw [dyadicToReal_max]
    exact hconvex.trans (max_le_max hleftCanonical hrightCanonical)
  have hcap' :
      realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))) ≤
        Dyadic.toReal parameters.precision
          (realCapUpper parameters.precision box.profileLeft box.lam).hi :=
    hcap.2
  rw [sparseUpperContourRowMajorant, gaussianCellRowUpperValue,
    dyadicToReal_min]
  simpa only [min_comm] using min_le_min hfourth hcap'

/-- The generic interval evaluator encloses one profile-endpoint row value on
any nonnegative positive-mesh segment.  Only the single box-level strict base
check remains executable. -/
theorem rowExpressionOnCell_contains
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {segment : Segment} {index : ℕ}
    (hstart : 0 ≤ segment.start) (hmesh : 0 < segment.mesh)
    (hbase : 0 < (UpperContourKernel.frac parameters.precision
      ((1 - box.lam) * (1 - box.lam))).lo)
    (profileQ : ℚ) (hprofileQ : 0 ≤ profileQ)
    {frequency : ℝ}
    (hfrequency : frequency ∈ Ioc
      ((segment.cellLeft index : ℚ) : ℝ)
      ((segment.cellRight index : ℚ) : ℝ)) :
    (rowExpressionOnCell parameters profileQ
      (segment.cellLeft index) (segment.cellRight index) box.lam).Contains
      (UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
        profileQ box.lam frequency) := by
  let frequencyLeft := segment.cellLeft index
  let frequencyRight := segment.cellRight index
  let frequencyInterval := Interval.enclose parameters.precision
    frequencyLeft frequencyRight
  have hleftNonneg : 0 ≤ frequencyLeft := by
    dsimp only [frequencyLeft, Segment.cellLeft]
    exact add_nonneg hstart (mul_nonneg (by positivity) hmesh.le)
  have hleftRight : frequencyLeft ≤ frequencyRight := by
    dsimp only [frequencyLeft, frequencyRight, Segment.cellRight]
    exact le_add_of_nonneg_right hmesh.le
  have hfrequencyInterval : frequencyInterval.Contains (frequencyLeft : ℝ) :=
    Interval.contains_enclose ⟨le_rfl, by exact_mod_cast hleftRight⟩
  have hfrequencyValid : frequencyInterval.Valid :=
    Interval.valid_of_contains hfrequencyInterval
  have hfrequencyLo : 0 ≤ frequencyInterval.lo :=
    Dyadic.roundDown_nonneg hleftNonneg
  have hsquareLo : 0 ≤ frequencyInterval.square.lo :=
    Interval.square_lo_nonneg_of_lo_nonneg hfrequencyValid hfrequencyLo
  have honeMinusLo : 0 ≤
      (UpperContourKernel.frac parameters.precision (1 - box.lam)).lo :=
    Dyadic.roundDown_nonneg (sub_nonneg.mpr facts.lam_lt_one.le)
  have hdenominator : 0 <
      (UpperContourKernel.frac parameters.precision
        ((1 - box.lam) * (1 - box.lam)) + frequencyInterval.square).lo :=
    add_pos_of_pos_of_nonneg hbase hsquareLo
  have hgaussianDenominator : 0 <
      ((UpperContourKernel.frac parameters.precision
        ((1 - box.lam) * (1 - box.lam)) +
          frequencyInterval.square).sqrt.sqrt).lo :=
    Interval.sqrt_lo_pos_of_lo_pos
      (Interval.sqrt_lo_pos_of_lo_pos hdenominator)
  have hrho : 0 ≤
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam) + frequencyInterval.square).lo :=
    add_nonneg (Dyadic.roundDown_nonneg (mul_self_nonneg box.lam)) hsquareLo
  apply UpperContourKernel.contains_normalizedFourthOrderRowBound
  · exact_mod_cast facts.lam_lt_one
  · exact ⟨hfrequency.1.le, hfrequency.2⟩
  · exact honeMinusLo
  · exact hdenominator
  · exact hgaussianDenominator
  · exact hrho
  · exact Or.inr (Dyadic.roundDown_nonneg hprofileQ)

/-- Concrete consumer form: geometry-local segment facts, one box-level base
check, and the profile cap imply the row-majorant bound automatically. -/
theorem sparseUpperContourRowMajorant_le_gaussianCellRowUpperValue_of_facts
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {segment : Segment} {index : ℕ}
    (hstart : 0 ≤ segment.start) (hmesh : 0 < segment.mesh)
    (hbase : 0 < (UpperContourKernel.frac parameters.precision
      ((1 - box.lam) * (1 - box.lam))).lo)
    {profile frequency : ℝ}
    (hprofile : profile ∈ Icc
      (box.profileLeft : ℝ) (box.profileRight : ℝ))
    (hfrequency : frequency ∈ Ioc
      ((segment.cellLeft index : ℚ) : ℝ)
      ((segment.cellRight index : ℚ) : ℝ))
    (hcap : (realCapUpper parameters.precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      gaussianCellRowUpperValue parameters box segment index := by
  have hprofileLeft : (0 : ℝ) ≤ box.profileLeft := by
    exact_mod_cast facts.profileLeft_nonneg
  have hleft := rowExpressionOnCell_contains facts hstart hmesh hbase
    box.profileLeft facts.profileLeft_nonneg hfrequency
  have hprofileRightNonneg : 0 ≤ box.profileRight := by
    exact_mod_cast hprofileLeft.trans (hprofile.1.trans hprofile.2)
  have hright := rowExpressionOnCell_contains facts hstart hmesh hbase
    box.profileRight hprofileRightNonneg hfrequency
  exact sparseUpperContourRowMajorant_le_gaussianCellRowUpperValue
    parameters box segment index profile frequency hprofileLeft hprofile
      (by exact_mod_cast facts.lam_lt_one) hleft hright hcap

/-- Literal upper rectangle represented by one segmented Gaussian cell. -/
noncomputable def gaussianCellRectangleValue
    (parameters : Parameters) (box : ProfileBox)
    (segment : Segment) (index : ℕ) : ℝ :=
  let frequencyLeft := segment.cellLeft index
  let alpha := box.sigma * box.sigma / 2
  (segment.mesh : ℝ) *
    Real.exp (-((alpha * frequencyLeft * frequencyLeft : ℚ) : ℝ)) *
    gaussianCellRowUpperValue parameters box segment index ^ parameters.rows *
    (1 / Real.sqrt
      (((box.lam * box.lam + frequencyLeft * frequencyLeft : ℚ) : ℝ)))

/-- Cellwise domination of the generic analytic integrand by the literal
left-endpoint rectangle encoded by a segmented cell. -/
theorem actualBoxQuadratureIntegrand_le_rectangle
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile frequency : ℝ} (hprofile : 0 ≤ profile)
    {segment : Segment} {index : ℕ}
    (hmesh : 0 ≤ segment.mesh)
    (hleft : 0 ≤ segment.cellLeft index)
    (hfrequency : ((segment.cellLeft index : ℚ) : ℝ) ≤ frequency)
    (hrow : sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      gaussianCellRowUpperValue parameters box segment index) :
    (segment.mesh : ℝ) *
        actualBoxQuadratureIntegrand parameters box profile frequency ≤
      gaussianCellRectangleValue parameters box segment index := by
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast facts.lam_pos
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast facts.lam_lt_one
  have hleftReal : 0 ≤ ((segment.cellLeft index : ℚ) : ℝ) := by
    exact_mod_cast hleft
  have hmeshReal : 0 ≤ (segment.mesh : ℝ) := by exact_mod_cast hmesh
  have hweight := gaussianQuadratureWeight_le_of_le
    (alpha := (box.sigma : ℝ) ^ 2 / 2)
    (lambda := (box.lam : ℝ))
    (frequencyLeft := ((segment.cellLeft index : ℚ) : ℝ))
    (frequency := frequency) (by positivity) hlam hleftReal hfrequency
  have hrowNonneg := SparseUpperContour.sparseUpperContourRowMajorant_nonneg
    (frequency := frequency) hprofile hlam.le hlamOne
  have hrowPower := pow_le_pow_left₀ hrowNonneg hrow parameters.rows
  have hweightLeftNonneg : 0 ≤
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) *
          ((segment.cellLeft index : ℚ) : ℝ) ^ 2) *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 +
          ((segment.cellLeft index : ℚ) : ℝ) ^ 2)) := by positivity
  have hproduct := mul_le_mul hweight hrowPower
    (pow_nonneg hrowNonneg parameters.rows) hweightLeftNonneg
  unfold actualBoxQuadratureIntegrand gaussianCellRectangleValue
  dsimp only
  calc
    _ = (segment.mesh : ℝ) *
        ((Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) *
          sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^
            parameters.rows) := by ring
    _ ≤ (segment.mesh : ℝ) *
        ((Real.exp (-((box.sigma : ℝ) ^ 2 / 2) *
            ((segment.cellLeft index : ℚ) : ℝ) ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 +
            ((segment.cellLeft index : ℚ) : ℝ) ^ 2))) *
          gaussianCellRowUpperValue parameters box segment index ^
            parameters.rows) :=
      mul_le_mul_of_nonneg_left hproduct hmeshReal
    _ = _ := by
      push_cast
      ring

/-- The first `count` cells of an arbitrary positive rational mesh dominate
the analytic integral over their exact half-open span. -/
theorem integral_Ioc_segmentPrefix_le_sum_rectangles
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    (segment : Segment) (count : ℕ)
    (hstart : 0 ≤ segment.start) (hmesh : 0 < segment.mesh)
    (hrow : ∀ index < count, ∀ frequency ∈
      Ioc (((segment.start + index * segment.mesh : ℚ) : ℝ))
        (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ)),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index) :
    (∫ frequency : ℝ in
      Ioc (segment.start : ℝ)
        ((segment.start + count * segment.mesh : ℚ) : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
      ∑ index ∈ Finset.range count,
        gaussianCellRectangleValue parameters box segment index := by
  have hintegrable := integrable_actualBoxQuadratureIntegrand facts hprofile
  induction count with
  | zero => simp
  | succ count ih =>
      have hrowPrevious : ∀ index < count, ∀ frequency ∈
          Ioc (((segment.start + index * segment.mesh : ℚ) : ℝ))
            (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ)),
          sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
            gaussianCellRowUpperValue parameters box segment index := by
        intro index hindex
        exact hrow index (hindex.trans count.lt_succ_self)
      have hprevious := ih hrowPrevious
      let left : ℝ :=
        ((segment.start + count * segment.mesh : ℚ) : ℝ)
      let right : ℝ :=
        ((segment.start + (count + 1) * segment.mesh : ℚ) : ℝ)
      let rectangle :=
        gaussianCellRectangleValue parameters box segment count
      have hleftRight : left ≤ right := by
        dsimp only [left, right]
        push_cast
        have hmeshReal : 0 ≤ (segment.mesh : ℝ) := by exact_mod_cast hmesh.le
        nlinarith
      have hcellPointwise : ∀ frequency ∈ Ioc left right,
          actualBoxQuadratureIntegrand parameters box profile frequency ≤
            rectangle / (segment.mesh : ℝ) := by
        intro frequency hfrequency
        apply (le_div_iff₀ (by exact_mod_cast hmesh)).2
        dsimp only [left, right, rectangle] at hfrequency ⊢
        have hcellLeft : segment.cellLeft count =
            segment.start + count * segment.mesh := rfl
        have hcellRight : segment.cellRight count =
            segment.start + (count + 1) * segment.mesh := by
          unfold Segment.cellRight Segment.cellLeft
          ring
        have hcellLeftNonneg : 0 ≤ segment.cellLeft count := by
          rw [hcellLeft]
          positivity
        simpa only [mul_comm] using
          actualBoxQuadratureIntegrand_le_rectangle facts hprofile hmesh.le
            hcellLeftNonneg hfrequency.1.le
            (hrow count count.lt_succ_self frequency (by
              simpa only [hcellLeft, hcellRight] using hfrequency))
      have hcell :
          (∫ frequency : ℝ in Ioc left right,
            actualBoxQuadratureIntegrand parameters box profile frequency) ≤
              rectangle := by
        calc
          _ ≤ ∫ _frequency : ℝ in Ioc left right,
              rectangle / (segment.mesh : ℝ) := by
            apply setIntegral_mono_on
            · exact hintegrable.integrableOn
            · exact integrableOn_const (hs := by
                rw [Real.volume_Ioc]
                exact ENNReal.ofReal_ne_top)
            · exact measurableSet_Ioc
            · exact hcellPointwise
          _ = rectangle := by
            rw [setIntegral_const]
            simp only [smul_eq_mul, Measure.real, Real.volume_Ioc]
            rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hleftRight)]
            dsimp only [left, right]
            push_cast
            field_simp
            ring
      have hstartLeft : (segment.start : ℝ) ≤ left := by
        dsimp only [left]
        push_cast
        have hmeshReal : 0 ≤ (segment.mesh : ℝ) := by exact_mod_cast hmesh.le
        nlinarith [mul_nonneg (Nat.cast_nonneg count) hmeshReal]
      have hdisjoint :
          Disjoint (Ioc (segment.start : ℝ) left) (Ioc left right) := by
        exact Set.disjoint_left.2 fun _ hfirst hsecond ↦
          (not_lt_of_ge hfirst.2) hsecond.1
      have hunion : Ioc (segment.start : ℝ) left ∪ Ioc left right =
          Ioc (segment.start : ℝ) right := by
        ext frequency
        simp only [Set.mem_union, Set.mem_Ioc]
        constructor
        · rintro (hfrequency | hfrequency)
          · exact ⟨hfrequency.1, hfrequency.2.trans hleftRight⟩
          · exact ⟨lt_of_le_of_lt hstartLeft hfrequency.1, hfrequency.2⟩
        · intro hfrequency
          by_cases hfrequencyLeft : frequency ≤ left
          · exact Or.inl ⟨hfrequency.1, hfrequencyLeft⟩
          · exact Or.inr ⟨lt_of_not_ge hfrequencyLeft, hfrequency.2⟩
      simp only [Nat.cast_add, Nat.cast_one] at hprevious ⊢
      change (∫ frequency : ℝ in Ioc (segment.start : ℝ) right,
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤ _
      rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioc
        hintegrable.integrableOn hintegrable.integrableOn]
      rw [Finset.sum_range_succ]
      exact add_le_add hprevious hcell

/-- One complete positive segment is bounded by its semantic rectangle sum. -/
theorem integral_Ioc_segment_le_sum_rectangles
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    (segment : Segment) (hstart : 0 ≤ segment.start)
    (hmesh : 0 < segment.mesh)
    (hrow : ∀ index < segment.count, ∀ frequency ∈
      Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index) :
    (∫ frequency : ℝ in Ioc (segment.start : ℝ)
      (segment.rightEndpoint : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
      ((List.range segment.count).map fun index ↦
        gaussianCellRectangleValue parameters box segment index).sum := by
  have hrow' : ∀ index < segment.count, ∀ frequency ∈
      Ioc (((segment.start + index * segment.mesh : ℚ) : ℝ))
        (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ)),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index := by
    intro index hindex frequency hfrequency
    apply hrow index hindex frequency
    convert hfrequency using 1 <;>
      simp only [Segment.cellLeft, Segment.cellRight] <;> push_cast <;> ring
  have h := integral_Ioc_segmentPrefix_le_sum_rectangles facts hprofile
    segment segment.count hstart hmesh hrow'
  rw [finset_sum_range_eq_list_sum_map] at h
  simpa [Segment.rightEndpoint] using h

/-- A family Gaussian cell encloses its literal segmented rectangle.  These
three dyadic sign conditions can be discharged uniformly or in bounded
kernel shards; no analytic proof is repeated per cell. -/
theorem gaussianCell_contains_rectangle
    {parameters : Parameters} {box : ProfileBox}
    {segment : Segment} {index : ℕ}
    (hrowUpper : 0 ≤
      (min (realCapUpper parameters.precision box.profileLeft box.lam).hi
        (max
          (rowExpressionOnCell parameters box.profileLeft
            (segment.cellLeft index) (segment.cellRight index) box.lam).hi
          (rowExpressionOnCell parameters box.profileRight
            (segment.cellLeft index) (segment.cellRight index) box.lam).hi)))
    (hbase : 0 ≤
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam +
          segment.cellLeft index * segment.cellLeft index)).lo)
    (hsqrt : 0 <
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam +
          segment.cellLeft index * segment.cellLeft index)).sqrt.lo) :
    (gaussianCell parameters box segment index).Contains
      (gaussianCellRectangleValue parameters box segment index) := by
  let frequencyLeft := segment.cellLeft index
  let alpha := box.sigma * box.sigma / 2
  let rowUpper :=
    min (realCapUpper parameters.precision box.profileLeft box.lam).hi
      (max
        (rowExpressionOnCell parameters box.profileLeft
          frequencyLeft (segment.cellRight index) box.lam).hi
        (rowExpressionOnCell parameters box.profileRight
          frequencyLeft (segment.cellRight index) box.lam).hi)
  have hmesh := Interval.contains_ofRat parameters.precision segment.mesh
  have hexp := Exp.negUpper_contains (p := parameters.precision) (k := 24)
    (x := alpha * frequencyLeft * frequencyLeft) (by
      dsimp only [alpha, frequencyLeft]
      have hsigmaSq : 0 ≤ box.sigma * box.sigma := mul_self_nonneg _
      have hfrequencySq :
          0 ≤ segment.cellLeft index * segment.cellLeft index :=
        mul_self_nonneg _
      calc
        0 ≤ (box.sigma * box.sigma / 2) *
            (segment.cellLeft index * segment.cellLeft index) := by positivity
        _ = (box.sigma * box.sigma / 2) * segment.cellLeft index *
            segment.cellLeft index := by ring)
  have hrow : (Interval.mk 0 rowUpper : Interval parameters.precision).Contains
      (Dyadic.toReal parameters.precision rowUpper) := by
    constructor
    · simpa only [rowUpper, Dyadic.toReal_zero] using
        (dyadicToReal_mono (precision := parameters.precision) hrowUpper)
    · rfl
  have hrowPower := UpperContourKernel.tensorPower_contains hrow
    parameters.rowOddPart parameters.rowSquareCount
  have hbaseInterval :
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam + frequencyLeft * frequencyLeft)).Contains
      (((box.lam * box.lam + frequencyLeft * frequencyLeft : ℚ) : ℝ)) :=
    Interval.contains_ofRat parameters.precision _
  have hsqrtInterval := Interval.contains_sqrt hbase hbaseInterval
  have hinverse :
      (UpperContourKernel.inverseSqrtAtLeft parameters.precision
        frequencyLeft box.lam).Contains
      (1 / Real.sqrt
        (((box.lam * box.lam + frequencyLeft * frequencyLeft : ℚ) : ℝ))) := by
    simpa [UpperContourKernel.inverseSqrtAtLeft, div_eq_mul_inv] using
      Interval.contains_reciprocal_of_pos hsqrt hsqrtInterval
  have hproduct := Interval.contains_mul
    (Interval.contains_mul (Interval.contains_mul hmesh hexp) hrowPower)
      hinverse
  simpa [gaussianCell, gaussianCellRectangleValue,
    gaussianCellRowUpperValue, frequencyLeft, alpha, rowUpper,
    Segment.cellLeft, Segment.cellRight, UpperContourKernel.frac,
    Parameters.rows] using hproduct

private theorem contains_foldl_add
    {precision : ℕ} {A : Type*} (xs : List A)
    (interval : A → Interval precision) (value : A → ℝ)
    (hvalue : ∀ x ∈ xs, (interval x).Contains (value x))
    {initial : Interval precision} {initialValue : ℝ}
    (hinitial : initial.Contains initialValue) :
    (xs.foldl (fun result x ↦ result + interval x) initial).Contains
      (xs.foldl (fun result x ↦ result + value x) initialValue) := by
  induction xs generalizing initial initialValue with
  | nil => exact hinitial
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro y hy
        exact hvalue y (List.mem_cons_of_mem x hy)
      · exact Interval.contains_add hinitial (hvalue x (by simp))

private theorem foldl_add_eq_add_sum_map
    {A : Type*} (xs : List A) (f : A → ℝ) (x : ℝ) :
    xs.foldl (fun result item ↦ result + f item) x =
      x + (xs.map f).sum := by
  induction xs generalizing x with
  | nil => simp
  | cons item xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring

private theorem sum_map_sum_eq_sum_flatMap
    {A B : Type*} (xs : List A) (g : A → List B) (f : B → ℝ) :
    (xs.map (fun item ↦ ((g item).map f).sum)).sum =
      ((xs.flatMap g).map f).sum := by
  induction xs with
  | nil => simp
  | cons item xs ih => simp [ih, List.sum_append]

/-- Literal rectangle sum corresponding to one bounded replay chunk. -/
noncomputable def segmentRectangleChunkValue
    (parameters : Parameters) (box : ProfileBox) (segment : Segment)
    (start count : ℕ) : ℝ :=
  (List.range count).foldl
    (fun result offset ↦ result +
      gaussianCellRectangleValue parameters box segment (start + offset)) 0

/-- Cell enclosures compose into one replay-chunk enclosure. -/
theorem segmentChunk_contains_rectangleChunk
    {parameters : Parameters} {box : ProfileBox} {segment : Segment}
    {start count : ℕ}
    (hcell : ∀ offset, offset < count →
      (gaussianCell parameters box segment (start + offset)).Contains
        (gaussianCellRectangleValue parameters box segment (start + offset))) :
    (segmentChunk parameters box segment start count).Contains
      (segmentRectangleChunkValue parameters box segment start count) := by
  have hzero : (UpperContourKernel.zero parameters.precision).Contains (0 : ℝ) := by
    simpa [UpperContourKernel.zero, UpperContourKernel.frac] using
      Interval.contains_ofRat parameters.precision (0 : ℚ)
  unfold segmentChunk segmentRectangleChunkValue
  exact contains_foldl_add (List.range count)
    (fun offset ↦ gaussianCell parameters box segment (start + offset))
    (fun offset ↦
      gaussianCellRectangleValue parameters box segment (start + offset))
    (fun offset hoffset ↦ hcell offset (List.mem_range.mp hoffset)) hzero

/-- Literal rectangle sum assigned to one chunk in `boxChunkPlan`. -/
noncomputable def boxRectangleChunkValue
    (parameters : Parameters) (box : ProfileBox) (chunk : Chunk) : ℝ :=
  segmentRectangleChunkValue parameters box
    (box.segments.getD chunk.segmentIndex default) chunk.start chunk.count

/-- Literal sum of all generated rectangle chunks in one box. -/
noncomputable def boxRectangleChunksValue
    (parameters : Parameters) (box : ProfileBox) : ℝ :=
  (boxChunkPlan box).foldl
    (fun result chunk ↦ result + boxRectangleChunkValue parameters box chunk) 0

/-- Literal rectangle sum in semantic segment order, independent of replay
chunk boundaries. -/
noncomputable def boxSegmentRectanglesValue
  (parameters : Parameters) (box : ProfileBox) : ℝ :=
  ((boxSegmentCells box).map
    (fun cell : Segment × ℕ ↦
      gaussianCellRectangleValue parameters box cell.1 cell.2)).sum

private theorem fold_chunk_rectangles_eq_covered_sum
    (parameters : Parameters) (box : ProfileBox) :
    boxRectangleChunksValue parameters box =
      ((boxChunkCells box).map
        (fun cell : Segment × ℕ ↦
          gaussianCellRectangleValue parameters box cell.1 cell.2)).sum := by
  unfold boxRectangleChunksValue boxRectangleChunkValue
    segmentRectangleChunkValue boxChunkCells chunkCells
  rw [foldl_add_eq_add_sum_map]
  simp only [zero_add]
  simp_rw [foldl_add_eq_add_sum_map, zero_add]
  have h := sum_map_sum_eq_sum_flatMap (boxChunkPlan box)
    (fun chunk ↦
      (List.range chunk.count).map fun offset =>
        (box.segments.getD chunk.segmentIndex default, chunk.start + offset))
    (fun cell : Segment × ℕ ↦
      gaussianCellRectangleValue parameters box cell.1 cell.2)
  simpa only [List.map_map, Function.comp_def] using h

/-- Exact chunk coverage identifies the replay rectangle sum with the
semantic segment rectangle sum. -/
theorem boxRectangleChunksValue_eq_segmentRectangles
    {parameters : Parameters} {box : ProfileBox}
    (hcoverage : boxChunkCells box = boxSegmentCells box) :
    boxRectangleChunksValue parameters box =
      boxSegmentRectanglesValue parameters box := by
  rw [fold_chunk_rectangles_eq_covered_sum parameters box, hcoverage]
  rfl

/-- Right endpoint of a nonempty segment list, exposed recursively so the
adjacency induction does not depend on list indexing. -/
private def lastSegmentEndpoint (first : Segment) : List Segment → ℚ
  | [] => first.rightEndpoint
  | next :: rest => lastSegmentEndpoint next rest

/-- Sum of analytic segment integrals in their prescribed order. -/
private noncomputable def segmentIntegralsValue
    (integrand : ℝ → ℝ) : List Segment → ℝ
  | [] => 0
  | segment :: rest =>
      (∫ frequency : ℝ in Ioc (segment.start : ℝ)
        (segment.rightEndpoint : ℝ), integrand frequency) +
        segmentIntegralsValue integrand rest

/-- Sum of literal rectangles in semantic segment order. -/
private noncomputable def segmentRectanglesValue
    (parameters : Parameters) (box : ProfileBox) : List Segment → ℝ
  | [] => 0
  | segment :: rest =>
      ((List.range segment.count).map fun index ↦
        gaussianCellRectangleValue parameters box segment index).sum +
        segmentRectanglesValue parameters box rest

private theorem start_le_lastSegmentEndpoint
    (first : Segment) (rest : List Segment)
    (hpositive : SegmentsPositive (first :: rest))
    (hadjacent : SegmentsAdjacent (first :: rest)) :
    first.start ≤ lastSegmentEndpoint first rest := by
  induction rest generalizing first with
  | nil =>
      rcases hpositive with ⟨hmesh, hcount, _⟩
      simp only [lastSegmentEndpoint, Segment.rightEndpoint]
      have hcountRat : (0 : ℚ) < first.count := by exact_mod_cast hcount
      nlinarith [mul_pos hcountRat hmesh]
  | cons next rest ih =>
      rcases hadjacent with ⟨hjoin, hadjacentRest⟩
      rcases hpositive with ⟨hmesh, hcount, hpositiveRest⟩
      simp only [lastSegmentEndpoint]
      have hfirstRight : first.start ≤ first.rightEndpoint := by
        unfold Segment.rightEndpoint
        have hcountRat : (0 : ℚ) < first.count := by exact_mod_cast hcount
        nlinarith [mul_pos hcountRat hmesh]
      exact hfirstRight.trans (hjoin.le.trans
        (ih next hpositiveRest hadjacentRest))

private theorem segments_start_nonneg
    (first : Segment) (rest : List Segment)
    (hfirst : 0 ≤ first.start)
    (hpositive : SegmentsPositive (first :: rest))
    (hadjacent : SegmentsAdjacent (first :: rest)) :
    ∀ segment ∈ first :: rest, 0 ≤ segment.start := by
  induction rest generalizing first with
  | nil => simpa using hfirst
  | cons next rest ih =>
      rcases hpositive with ⟨hmesh, hcount, hpositiveRest⟩
      rcases hadjacent with ⟨hjoin, hadjacentRest⟩
      have hnext : 0 ≤ next.start := by
        rw [← hjoin]
        unfold Segment.rightEndpoint
        have hcountRat : (0 : ℚ) < first.count := by exact_mod_cast hcount
        nlinarith [mul_pos hcountRat hmesh]
      intro segment hsegment
      rcases List.mem_cons.mp hsegment with rfl | hsegment
      · exact hfirst
      · exact ih next hnext hpositiveRest hadjacentRest segment hsegment

private theorem segment_mesh_pos_of_mem
    {segments : List Segment} (hpositive : SegmentsPositive segments)
    {segment : Segment} (hsegment : segment ∈ segments) :
    0 < segment.mesh := by
  induction segments with
  | nil => simp at hsegment
  | cons first rest ih =>
      rcases hpositive with ⟨hmesh, _hcount, hpositiveRest⟩
      rcases List.mem_cons.mp hsegment with rfl | hsegment
      · exact hmesh
      · exact ih hpositiveRest hsegment

/-- Exact box geometry supplies the nonnegative start and positive mesh facts
needed by every analytic row-expression consumer. -/
theorem segment_numeric_facts_of_geometry
    {box : ProfileBox} (geometry : SegmentGeometry box)
    {segment : Segment} (hsegment : segment ∈ box.segments) :
    0 ≤ segment.start ∧ 0 < segment.mesh := by
  rcases geometry with
    ⟨_hchunk, hnonempty, hfirst, hpositive, hadjacent, _hlast, _hcutoff⟩
  constructor
  · cases hsegments : box.segments with
    | nil => simp [hsegments] at hnonempty
    | cons first rest =>
        have hpositive' : SegmentsPositive (first :: rest) := by
          simpa [hsegments] using hpositive
        have hadjacent' : SegmentsAdjacent (first :: rest) := by
          simpa [hsegments] using hadjacent
        have hfirst' : first.start = 0 := by
          simpa [hsegments] using hfirst
        exact segments_start_nonneg first rest hfirst'.symm.le
          hpositive' hadjacent' segment (by simpa [hsegments] using hsegment)
  · exact segment_mesh_pos_of_mem hpositive hsegment

/-- End-to-end row-majorant constructor for generated boxes.  Geometry and a
single box-level Boolean replace all per-cell analytic side-condition proofs. -/
theorem boxRowMajorant_of_geometry_and_baseCheck
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (geometry : SegmentGeometry box)
    (hbase : rowExpressionBaseCheck parameters box = true)
    (hcap : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper parameters.precision box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      ∀ segment ∈ box.segments, ∀ index < segment.count,
      ∀ frequency ∈ Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index := by
  intro profile hprofile segment hsegment index _hindex frequency hfrequency
  obtain ⟨hstart, hmesh⟩ :=
    segment_numeric_facts_of_geometry geometry hsegment
  exact sparseUpperContourRowMajorant_le_gaussianCellRowUpperValue_of_facts
    facts hstart hmesh (rowExpressionBaseCheck_sound hbase)
      hprofile hfrequency (hcap profile hprofile)

/-- Every semantic cell in a valid box encloses its Gaussian rectangle.  The
only executable positivity premise is the box-level lower endpoint for
`lam^2`; all frequency-dependent sign conditions follow analytically. -/
theorem gaussianCell_contains_rectangle_of_facts
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (geometry : SegmentGeometry box)
    (hrowBase : rowExpressionBaseCheck parameters box = true)
    (hlambdaBase : lambdaSquareBaseCheck parameters box = true)
    (hcap : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper parameters.precision box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))))
    {segment : Segment} (hsegment : segment ∈ box.segments)
    {index : ℕ} (_hindex : index < segment.count) :
    (gaussianCell parameters box segment index).Contains
      (gaussianCellRectangleValue parameters box segment index) := by
  obtain ⟨hstart, hmesh⟩ :=
    segment_numeric_facts_of_geometry geometry hsegment
  have hfrequency : ((segment.cellRight index : ℚ) : ℝ) ∈
      Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ) := by
    constructor
    · exact_mod_cast (show segment.cellLeft index < segment.cellRight index by
        simp only [Segment.cellRight]
        linarith)
    · exact le_rfl
  have expressionUpper_nonneg
      (profile : ℚ) (hprofile : 0 ≤ profile) :
      0 ≤ (rowExpressionOnCell parameters profile
        (segment.cellLeft index) (segment.cellRight index) box.lam).hi := by
    have hcontains := rowExpressionOnCell_contains facts hstart hmesh
      (rowExpressionBaseCheck_sound hrowBase) profile hprofile hfrequency
    have hmajorantNonneg :
        0 ≤ UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
          profile box.lam ((segment.cellRight index : ℚ) : ℝ) := by
      rw [normalizedFourthOrderRowBound_eq_sparseUpperMajorant profile box.lam _
        (by exact_mod_cast facts.lam_lt_one)]
      exact (SparseUpperContour.sparseUpperContourRowMajorant_nonneg
        (by exact_mod_cast hprofile)
        (by exact_mod_cast facts.lam_pos.le)
        (by exact_mod_cast facts.lam_lt_one)).trans (min_le_left _ _)
    exact dyadic_nonneg_of_toReal_nonneg (hmajorantNonneg.trans hcontains.2)
  have hprofileRightNonneg : 0 ≤ box.profileRight :=
    facts.profileLeft_nonneg.trans facts.profileLeft_le_right
  have hleftUpper := expressionUpper_nonneg box.profileLeft
    facts.profileLeft_nonneg
  have hrightUpper := expressionUpper_nonneg box.profileRight
    hprofileRightNonneg
  have hcapLeft := hcap (box.profileLeft : ℝ) ⟨le_rfl, by
    exact_mod_cast facts.profileLeft_le_right⟩
  have hcapValueNonneg : 0 ≤ realRowDeficitCap
      (Real.sqrt (box.profileLeft : ℝ) * (box.lam : ℝ) /
        (1 - (box.lam : ℝ))) := by
    unfold realRowDeficitCap
    positivity
  have hcapUpper : 0 ≤
      (realCapUpper parameters.precision box.profileLeft box.lam).hi :=
    dyadic_nonneg_of_toReal_nonneg (hcapValueNonneg.trans hcapLeft.2)
  have hrowUpper : 0 ≤
      min (realCapUpper parameters.precision box.profileLeft box.lam).hi
        (max
          (rowExpressionOnCell parameters box.profileLeft
            (segment.cellLeft index) (segment.cellRight index) box.lam).hi
          (rowExpressionOnCell parameters box.profileRight
            (segment.cellLeft index) (segment.cellRight index) box.lam).hi) :=
    le_min hcapUpper (hleftUpper.trans (le_max_left _ _))
  have hbase : 0 ≤
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam +
          segment.cellLeft index * segment.cellLeft index)).lo := by
    simpa [UpperContourKernel.frac, Interval.ofRat, Interval.enclose] using
      Dyadic.roundDown_nonneg (add_nonneg (mul_self_nonneg box.lam)
        (mul_self_nonneg (segment.cellLeft index)))
  have hlambdaLoLe :
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam)).lo ≤
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam +
          segment.cellLeft index * segment.cellLeft index)).lo := by
    simp only [UpperContourKernel.frac, Interval.ofRat, Interval.enclose,
      Dyadic.roundDown]
    apply Int.floor_mono
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (mul_self_nonneg (segment.cellLeft index)))
      (by positivity)
  have hcombinedPos : 0 <
      (UpperContourKernel.frac parameters.precision
        (box.lam * box.lam +
          segment.cellLeft index * segment.cellLeft index)).lo :=
    (lambdaSquareBaseCheck_sound hlambdaBase).trans_le hlambdaLoLe
  exact gaussianCell_contains_rectangle hrowUpper hbase
    (Interval.sqrt_lo_pos_of_lo_pos hcombinedPos)

/-- Exact chunk coverage transports the semantic-cell enclosure to every
generated replay reference, ruling out the `getD default` fallback. -/
theorem boxGaussianCellsContainRectangles_of_facts
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (geometry : SegmentGeometry box)
    (coverage : boxChunkCells box = boxSegmentCells box)
    (hrowBase : rowExpressionBaseCheck parameters box = true)
    (hlambdaBase : lambdaSquareBaseCheck parameters box = true)
    (hcap : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper parameters.precision box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    ∀ chunk ∈ boxChunkPlan box, ∀ offset,
      offset < chunk.count →
      (gaussianCell parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)).Contains
      (gaussianCellRectangleValue parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)) := by
  intro chunk hchunk offset hoffset
  let segment := box.segments.getD chunk.segmentIndex default
  let index := chunk.start + offset
  have hplanned : (segment, index) ∈ boxChunkCells box := by
    unfold boxChunkCells
    apply List.mem_flatMap.mpr
    refine ⟨chunk, hchunk, ?_⟩
    unfold chunkCells
    exact List.mem_map.mpr ⟨offset, List.mem_range.mpr hoffset, rfl⟩
  have hsemantic : (segment, index) ∈ boxSegmentCells box := by
    rw [← coverage]
    exact hplanned
  unfold boxSegmentCells at hsemantic
  rcases List.mem_flatMap.mp hsemantic with
    ⟨semanticSegment, hsemanticSegment, hsemanticCell⟩
  rcases List.mem_map.mp hsemanticCell with
    ⟨semanticIndex, hsemanticIndex, hpair⟩
  have hsegmentEq : semanticSegment = segment := congrArg Prod.fst hpair
  have hindexEq : semanticIndex = index := congrArg Prod.snd hpair
  have hsegment : segment ∈ box.segments := by
    rw [← hsegmentEq]
    exact hsemanticSegment
  have hindex : index < segment.count := by
    rw [← hsegmentEq, ← hindexEq]
    exact List.mem_range.mp hsemanticIndex
  exact gaussianCell_contains_rectangle_of_facts facts geometry hrowBase
    hlambdaBase hcap hsegment hindex

private theorem lastSegmentEndpoint_eq_getLast
    (first : Segment) (rest : List Segment) :
    lastSegmentEndpoint first rest = (first :: rest).getLast!.rightEndpoint := by
  induction rest generalizing first with
  | nil => simp [lastSegmentEndpoint]
  | cons next rest ih =>
      simp only [lastSegmentEndpoint]
      rw [ih]
      simp

/-- Adjacent positive segments integrate exactly as the sum of their
individual half-open intervals. -/
private theorem integral_Ioc_segments_eq_sum
    (integrand : ℝ → ℝ) (hintegrable : Integrable integrand)
    (first : Segment) (rest : List Segment)
    (hpositive : SegmentsPositive (first :: rest))
    (hadjacent : SegmentsAdjacent (first :: rest)) :
    (∫ frequency : ℝ in Ioc (first.start : ℝ)
      (lastSegmentEndpoint first rest : ℝ), integrand frequency) =
      segmentIntegralsValue integrand (first :: rest) := by
  induction rest generalizing first with
  | nil => simp [lastSegmentEndpoint, segmentIntegralsValue]
  | cons next rest ih =>
      rcases hpositive with ⟨hmesh, hcount, hpositiveRest⟩
      rcases hadjacent with ⟨hjoin, hadjacentRest⟩
      have hrest := ih next hpositiveRest hadjacentRest
      have hfirstRight : (first.start : ℝ) ≤ first.rightEndpoint := by
        exact_mod_cast (by
          unfold Segment.rightEndpoint
          have hcountRat : (0 : ℚ) < first.count := by exact_mod_cast hcount
          nlinarith [mul_pos hcountRat hmesh] :
            first.start ≤ first.rightEndpoint)
      have hrestEnd : (next.start : ℝ) ≤
          (lastSegmentEndpoint next rest : ℝ) := by
        exact_mod_cast start_le_lastSegmentEndpoint next rest
          hpositiveRest hadjacentRest
      have hjoinReal : (first.rightEndpoint : ℝ) = next.start := by
        exact_mod_cast hjoin
      have hdisjoint : Disjoint
          (Ioc (first.start : ℝ) (first.rightEndpoint : ℝ))
          (Ioc (next.start : ℝ) (lastSegmentEndpoint next rest : ℝ)) := by
        exact Set.disjoint_left.2 fun _ hleft hright ↦
          (not_lt_of_ge (hjoinReal ▸ hleft.2)) hright.1
      have hunion :
          Ioc (first.start : ℝ) (first.rightEndpoint : ℝ) ∪
            Ioc (next.start : ℝ) (lastSegmentEndpoint next rest : ℝ) =
          Ioc (first.start : ℝ) (lastSegmentEndpoint next rest : ℝ) := by
        ext frequency
        simp only [Set.mem_union, Set.mem_Ioc]
        constructor
        · rintro (hfrequency | hfrequency)
          · exact ⟨hfrequency.1,
              hfrequency.2.trans (hjoinReal.le.trans hrestEnd)⟩
          · exact ⟨lt_of_le_of_lt (hfirstRight.trans hjoinReal.le)
              hfrequency.1, hfrequency.2⟩
        · intro hfrequency
          by_cases hfrequencyJoin : frequency ≤ (first.rightEndpoint : ℝ)
          · exact Or.inl ⟨hfrequency.1, hfrequencyJoin⟩
          · exact Or.inr ⟨by
              rw [← hjoinReal]
              exact lt_of_not_ge hfrequencyJoin, hfrequency.2⟩
      simp only [lastSegmentEndpoint]
      change (∫ frequency : ℝ in
          Ioc (first.start : ℝ) (lastSegmentEndpoint next rest : ℝ),
          integrand frequency) =
        (∫ frequency : ℝ in
          Ioc (first.start : ℝ) (first.rightEndpoint : ℝ),
          integrand frequency) +
        segmentIntegralsValue integrand (next :: rest)
      rw [← hrest, ← hunion,
        setIntegral_union hdisjoint measurableSet_Ioc
          hintegrable.integrableOn hintegrable.integrableOn]

private theorem sum_segment_integrals_le_rectangles
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    (segments : List Segment)
    (hstart : ∀ segment ∈ segments, 0 ≤ segment.start)
    (hpositive : SegmentsPositive segments)
    (hrow : ∀ segment ∈ segments, ∀ index < segment.count,
      ∀ frequency ∈ Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index) :
    segmentIntegralsValue
        (actualBoxQuadratureIntegrand parameters box profile) segments ≤
      segmentRectanglesValue parameters box segments := by
  induction segments with
  | nil => simp [segmentIntegralsValue, segmentRectanglesValue]
  | cons segment rest ih =>
      rcases hpositive with ⟨hmesh, _hcount, hpositiveRest⟩
      simp only [segmentIntegralsValue, segmentRectanglesValue]
      apply add_le_add
      · exact integral_Ioc_segment_le_sum_rectangles facts hprofile segment
          (hstart segment (by simp)) hmesh
          (fun index hindex frequency hfrequency ↦
            hrow segment (by simp) index hindex frequency hfrequency)
      · apply ih
        · intro item hitem
          exact hstart item (List.mem_cons_of_mem segment hitem)
        · exact hpositiveRest
        · intro item hitem
          exact hrow item (List.mem_cons_of_mem segment hitem)

private theorem boxSegmentRectanglesValue_eq_recursive
    (parameters : Parameters) (box : ProfileBox) :
    boxSegmentRectanglesValue parameters box =
      segmentRectanglesValue parameters box box.segments := by
  unfold boxSegmentRectanglesValue boxSegmentCells
  have h := sum_map_sum_eq_sum_flatMap box.segments
    (fun segment ↦
      (List.range segment.count).map fun index => (segment, index))
    (fun cell : Segment × ℕ ↦
      gaussianCellRectangleValue parameters box cell.1 cell.2)
  rw [← h]
  induction box.segments with
  | nil => simp [segmentRectanglesValue]
  | cons segment rest ih =>
      simp only [List.map_cons, List.sum_cons, segmentRectanglesValue]
      rw [ih]
      simp only [List.map_map, Function.comp_apply, Function.comp_def]

/-- Chunkwise enclosures compose into the finite part of `boxIntegral`. -/
theorem boxComputedChunks_contains_rectangleChunks
    {parameters : Parameters} {box : ProfileBox}
    (hchunk : ∀ chunk ∈ boxChunkPlan box,
      (boxChunkValue parameters box chunk).Contains
        (boxRectangleChunkValue parameters box chunk)) :
    ((boxComputedChunks parameters box).foldl
      (fun result chunk ↦ result + chunk)
      (UpperContourKernel.zero parameters.precision)).Contains
        (boxRectangleChunksValue parameters box) := by
  have hzero : (UpperContourKernel.zero parameters.precision).Contains (0 : ℝ) := by
    simpa [UpperContourKernel.zero, UpperContourKernel.frac] using
      Interval.contains_ofRat parameters.precision (0 : ℚ)
  unfold boxComputedChunks boxRectangleChunksValue
  rw [List.foldl_map]
  exact contains_foldl_add (boxChunkPlan box)
    (boxChunkValue parameters box) (boxRectangleChunkValue parameters box)
    hchunk hzero

/-- Literal Gaussian-tail surrogate encoded after all frequency segments. -/
noncomputable def boxTailValue
    (parameters : Parameters) (box : ProfileBox) (profile : ℝ) : ℝ :=
  let alpha := box.sigma * box.sigma / 2
  realRowDeficitCap
      (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))) ^
      parameters.rows *
    Real.exp (-(((alpha * box.cutoff * box.cutoff : ℚ) : ℝ))) *
    (((1 / (2 * (alpha * box.cutoff * box.cutoff)) : ℚ) : ℝ))

/-- The literal Gaussian tail dominates the analytic integrand beyond the
box cutoff for arbitrary factored row counts. -/
theorem integral_Ioi_actualBoxQuadratureIntegrand_le_boxTailValue
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    (hcutoff : 0 < box.cutoff) :
    (∫ frequency : ℝ in Ioi (box.cutoff : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        boxTailValue parameters box profile := by
  let cap := realRowDeficitCap
    (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))
  let upper : ℝ → ℝ := fun frequency ↦
    cap ^ parameters.rows *
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
      (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast facts.lam_pos
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast facts.lam_lt_one
  have hsigma : 0 < (box.sigma : ℝ) := by exact_mod_cast facts.sigma_pos
  have hcutoffReal : 0 < (box.cutoff : ℝ) := by exact_mod_cast hcutoff
  have hcapNonneg : 0 ≤ cap := by
    dsimp only [cap]
    unfold realRowDeficitCap
    positivity
  have hupperMeasurable : AEStronglyMeasurable upper := by
    apply Measurable.aestronglyMeasurable
    dsimp only [upper]
    fun_prop
  have hupperIntegrable : IntegrableOn upper (Ioi (box.cutoff : ℝ)) := by
    let dominating : ℝ → ℝ := fun frequency ↦
      (cap ^ parameters.rows / (box.lam : ℝ)) *
        Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2)
    have hdominating : Integrable dominating :=
      (integrable_exp_neg_mul_sq
        (by positivity : 0 < (box.sigma : ℝ) ^ 2 / 2)).const_mul _
    apply hdominating.integrableOn.mono' hupperMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with frequency _
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hsqrt : (box.lam : ℝ) ≤
          Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) :=
        (Real.le_sqrt hlam.le (by positivity)).2
          (by nlinarith [sq_nonneg frequency])
      have hinverse := one_div_le_one_div_of_le hlam hsqrt
      dsimp only [upper, dominating]
      calc
        _ ≤ cap ^ parameters.rows *
            Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
            (1 / (box.lam : ℝ)) := by gcongr
        _ = _ := by ring
    · dsimp only [upper]
      positivity
  have hactualIntegrable : IntegrableOn
      (actualBoxQuadratureIntegrand parameters box profile)
      (Ioi (box.cutoff : ℝ)) :=
    (integrable_actualBoxQuadratureIntegrand facts hprofile).integrableOn
  have hpointwise : ∀ frequency ∈ Ioi (box.cutoff : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency ≤
        upper frequency := by
    intro frequency _
    have hrowNonneg := SparseUpperContour.sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne
    have hrowCap :
        sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤ cap :=
      min_le_right _ _
    have hpower := pow_le_pow_left₀ hrowNonneg hrowCap parameters.rows
    unfold actualBoxQuadratureIntegrand
    dsimp only [upper]
    calc
      _ ≤ Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          cap ^ parameters.rows *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpower (Real.exp_nonneg _)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ frequency : ℝ in Ioi (box.cutoff : ℝ), upper frequency :=
      setIntegral_mono_on hactualIntegrable hupperIntegrable measurableSet_Ioi
        hpointwise
    _ ≤ cap ^ parameters.rows *
        Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * (box.cutoff : ℝ) ^ 2) /
          (2 * ((box.sigma : ℝ) ^ 2 / 2) * (box.cutoff : ℝ) ^ 2) := by
      exact _root_.CertifiedJL.integral_Ioi_gaussianQuadratureWeight_le
        (halpha := by positivity) hlam hcutoffReal
          (pow_nonneg hcapNonneg parameters.rows)
    _ = boxTailValue parameters box profile := by
      unfold boxTailValue
      dsimp only [cap]
      push_cast
      ring

/-- Exact segment adjacency and chunk coverage eliminate the last analytic
quadrature premise: finite rectangles plus the checked Gaussian tail dominate
the complete positive-frequency integral. -/
theorem integral_Ioi_zero_actualBoxQuadratureIntegrand_le
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (geometry : SegmentGeometry box)
    (coverage : boxChunkCells box = boxSegmentCells box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    (hrow : ∀ segment ∈ box.segments, ∀ index < segment.count,
      ∀ frequency ∈ Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index) :
    (∫ frequency : ℝ in Ioi 0,
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
      boxRectangleChunksValue parameters box +
        boxTailValue parameters box profile := by
  rcases geometry with
    ⟨_hchunk, hnonempty, hfirst, hpositive, hadjacent, hlast, hcutoff⟩
  have hintegrable := integrable_actualBoxQuadratureIntegrand facts hprofile
  cases hsegments : box.segments with
  | nil => simp [hsegments] at hnonempty
  | cons first rest =>
      have hpositive' : SegmentsPositive (first :: rest) := by
        simpa [hsegments] using hpositive
      have hadjacent' : SegmentsAdjacent (first :: rest) := by
        simpa [hsegments] using hadjacent
      have hfirst' : first.start = 0 := by
        simpa [hsegments] using hfirst
      have hlast' : (first :: rest).getLast!.rightEndpoint = box.cutoff := by
        simpa [hsegments] using hlast
      have hstarts : ∀ segment ∈ first :: rest, 0 ≤ segment.start :=
        segments_start_nonneg first rest hfirst'.symm.le hpositive' hadjacent'
      have hsegmentIntegral := integral_Ioc_segments_eq_sum
        (actualBoxQuadratureIntegrand parameters box profile) hintegrable
        first rest hpositive' hadjacent'
      rw [lastSegmentEndpoint_eq_getLast, hlast', hfirst'] at hsegmentIntegral
      have hsegmentBound := sum_segment_integrals_le_rectangles
        facts hprofile (first :: rest) hstarts hpositive' (by
          intro segment hsegment index hindex frequency hfrequency
          exact hrow segment (by simpa [hsegments] using hsegment)
            index hindex frequency hfrequency)
      have hfinite :
          (∫ frequency : ℝ in Ioc 0 (box.cutoff : ℝ),
            actualBoxQuadratureIntegrand parameters box profile frequency) ≤
            boxRectangleChunksValue parameters box := by
        calc
          _ = segmentIntegralsValue
              (actualBoxQuadratureIntegrand parameters box profile)
              (first :: rest) := by simpa using hsegmentIntegral
          _ ≤ segmentRectanglesValue parameters box (first :: rest) :=
            hsegmentBound
          _ = boxSegmentRectanglesValue parameters box := by
            rw [boxSegmentRectanglesValue_eq_recursive parameters box,
              hsegments]
          _ = boxRectangleChunksValue parameters box :=
            (boxRectangleChunksValue_eq_segmentRectangles coverage).symm
      have htail := integral_Ioi_actualBoxQuadratureIntegrand_le_boxTailValue
        facts hprofile hcutoff
      have hcutoffReal : (0 : ℝ) < box.cutoff := by exact_mod_cast hcutoff
      have hdisjoint : Disjoint (Ioc (0 : ℝ) (box.cutoff : ℝ))
          (Ioi (box.cutoff : ℝ)) := by
        exact Set.disjoint_left.2 fun _ hleft hright ↦
          (not_lt_of_ge hleft.2) hright
      have hunion : Ioc (0 : ℝ) (box.cutoff : ℝ) ∪
          Ioi (box.cutoff : ℝ) = Ioi 0 := by
        ext frequency
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (hfrequency | hfrequency)
          · exact hfrequency.1
          · exact hcutoffReal.trans hfrequency
        · intro hfrequency
          by_cases hfrequencyCutoff : frequency ≤ (box.cutoff : ℝ)
          · exact Or.inl ⟨hfrequency, hfrequencyCutoff⟩
          · exact Or.inr (lt_of_not_ge hfrequencyCutoff)
      rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioi
        hintegrable.integrableOn hintegrable.integrableOn]
      exact add_le_add hfinite htail

/-- Once the real cap is enclosed, the executable tail encloses its literal
Gaussian-tail surrogate for arbitrary factored row counts. -/
theorem boxTail_contains
    {parameters : Parameters} {box : ProfileBox} {profile : ℝ}
    (hcap : (realCapUpper parameters.precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    (UpperContourKernel.tensorPower
        (realCapUpper parameters.precision box.profileLeft box.lam)
        parameters.rowOddPart parameters.rowSquareCount *
      Exp.negUpper parameters.precision
        ((box.sigma * box.sigma / 2) * box.cutoff * box.cutoff) 28 *
      UpperContourKernel.frac parameters.precision
        (1 / (2 * ((box.sigma * box.sigma / 2) *
          box.cutoff * box.cutoff)))).Contains
      (boxTailValue parameters box profile) := by
  have hcapPower := UpperContourKernel.tensorPower_contains hcap
    parameters.rowOddPart parameters.rowSquareCount
  have hexp := Exp.negUpper_contains (p := parameters.precision) (k := 28)
    (x := (box.sigma * box.sigma / 2) * box.cutoff * box.cutoff) (by
      have hsigmaSq : 0 ≤ box.sigma * box.sigma := mul_self_nonneg _
      have hcutoffSq : 0 ≤ box.cutoff * box.cutoff := mul_self_nonneg _
      nlinarith)
  have hfactor := Interval.contains_ofRat parameters.precision
    (1 / (2 * ((box.sigma * box.sigma / 2) *
      box.cutoff * box.cutoff)) : ℚ)
  have hproduct := Interval.contains_mul
    (Interval.contains_mul hcapPower hexp) hfactor
  simpa [boxTailValue, UpperContourKernel.frac, Parameters.rows] using hproduct

/-- The complete executable integral contains the finite rectangle sum plus
the literal Gaussian tail. -/
theorem boxIntegral_contains_rectangleChunks_add_tail
    {parameters : Parameters} {box : ProfileBox} {profile : ℝ}
    (hchunk : ∀ chunk ∈ boxChunkPlan box,
      (boxChunkValue parameters box chunk).Contains
        (boxRectangleChunkValue parameters box chunk))
    (hcap : (realCapUpper parameters.precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    (boxIntegral parameters box).Contains
      (boxRectangleChunksValue parameters box +
        boxTailValue parameters box profile) := by
  have hfinite := boxComputedChunks_contains_rectangleChunks hchunk
  have htail := boxTail_contains (parameters := parameters) (box := box) hcap
  unfold boxIntegral boxIntegralFrom
  dsimp only
  exact Interval.contains_add hfinite htail

/-- The generic contour reduction bounds the security-scaled probability by
the literal prefactor times the positive-frequency integral. -/
theorem scaledUpperTailProbability_le_actualBoxEndpoint
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {d : ℕ} (a : Fin d → ℝ) (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : sparseProfileFourthMoment a ∈
      Icc (box.profileLeft : ℝ) (box.profileRight : ℝ)) :
    scaledUpperTailProbability parameters a ≤
      boxActualPrefactorValue parameters box *
        (∫ frequency : ℝ in Ioi 0,
          actualBoxQuadratureIntegrand parameters box
            (sparseProfileFourthMoment a) frequency) := by
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast facts.lam_pos
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast facts.lam_lt_one
  have hsigma : 0 < (box.sigma : ℝ) := by exact_mod_cast facts.sigma_pos
  have hprofileNonneg : 0 ≤ sparseProfileFourthMoment a := by
    have hleft : (0 : ℝ) ≤ box.profileLeft := by
      exact_mod_cast facts.profileLeft_nonneg
    exact hleft.trans hprofile.1
  have hfourth : ∀ frequency : ℝ,
      Real.sqrt (1 - (box.lam : ℝ)) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ ↦ realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a) (box.lam : ℝ) frequency := by
    intro frequency
    apply normalized_rowMGF_le_fourthOrderMajorant_of_error
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
      sub_zero, add_zero] using
      sparseUpper_fourthOrder a hnorm
        (s := (box.lam : ℝ) + frequency * Complex.I)
        (by simpa using (show (0 : ℝ) ≤ box.lam by
          exact_mod_cast facts.lam_pos.le))
        (by simpa using (show (box.lam : ℝ) < 1 by
          exact_mod_cast facts.lam_lt_one))
  let contour : ℝ → ℝ := fun frequency ↦
    ‖shiftedGaussianContourWeight (box.sigma : ℝ) (box.theta : ℝ)
      (parameters.threshold : ℝ) (box.lam : ℝ) frequency‖ *
      ‖quadraticComplexMGF
        (fun row : Fin d → ℤ ↦ realRowDot row a)
        (sparseRademacherRow d).toMeasure
        ((box.lam : ℝ) + frequency * Complex.I) ^ parameters.rows‖
  let coefficient : ℝ :=
    (1 / (2 * Real.pi * standardGaussianCDF (box.theta : ℝ))) *
      Real.exp (-((box.lam : ℝ) * ((parameters.threshold : ℝ) -
        (box.theta : ℝ) * (box.sigma : ℝ)) -
          (box.sigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
      (1 / Real.sqrt (1 - (box.lam : ℝ))) ^ parameters.rows
  have hpointwise : ∀ frequency : ℝ, contour frequency ≤
      coefficient * actualBoxQuadratureIntegrand parameters box
        (sparseProfileFourthMoment a) frequency := by
    intro frequency
    have hnormalized := normalized_rowMGF_le_contourRowMajorant
      a hlam.le hlamOne hnorm (hfourth frequency)
    have hsqrt : 0 < Real.sqrt (1 - (box.lam : ℝ)) :=
      Real.sqrt_pos.2 (sub_pos.mpr hlamOne)
    have hnormLe :
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ ↦ realRowDot row a)
          (sparseRademacherRow d).toMeasure
          ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        (1 / Real.sqrt (1 - (box.lam : ℝ))) *
          sparseUpperContourRowMajorant
            (sparseProfileFourthMoment a) (box.lam : ℝ) frequency := by
      rw [one_div, inv_mul_eq_div]
      exact (le_div_iff₀ hsqrt).2 (by simpa [mul_comm] using hnormalized)
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hnormLe parameters.rows
    have hCDF : 0 < standardGaussianCDF (box.theta : ℝ) :=
      standardGaussianCDF_pos _
    have hden : 0 < Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) := by
      positivity
    have hcommon : 0 ≤
        (1 / (2 * Real.pi * standardGaussianCDF (box.theta : ℝ))) *
          Real.exp (-((box.lam : ℝ) * ((parameters.threshold : ℝ) -
            (box.theta : ℝ) * (box.sigma : ℝ)) -
              (box.sigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
          Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) := by
      positivity
    dsimp only [contour, coefficient]
    rw [norm_shiftedGaussianContourWeight_eq_quadrature, norm_pow]
    unfold actualBoxQuadratureIntegrand
    calc
      _ ≤ (1 / (2 * Real.pi * standardGaussianCDF (box.theta : ℝ))) *
          Real.exp (-((box.lam : ℝ) * ((parameters.threshold : ℝ) -
            (box.theta : ℝ) * (box.sigma : ℝ)) -
              (box.sigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
          Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) *
          ((1 / Real.sqrt (1 - (box.lam : ℝ))) *
            sparseUpperContourRowMajorant
              (sparseProfileFourthMoment a) (box.lam : ℝ) frequency) ^
                parameters.rows := by
        exact mul_le_mul_of_nonneg_left hpow hcommon
      _ = _ := by ring
  have hcontour :=
    sparseRademacherMatrix_realProjectionSqNorm_toReal_le_positiveContour
      (m := parameters.rows) a (sigma := (box.sigma : ℝ))
      (theta := (box.theta : ℝ)) (t := (parameters.threshold : ℝ))
      (lambda := (box.lam : ℝ)) hsigma hlam
  have hcontourInt : Integrable contour :=
    integrable_sparseUpperContourNorm a parameters.rows hlam hsigma
  have hactualInt := integrable_actualBoxQuadratureIntegrand facts hprofileNonneg
  have hintegral : (∫ frequency : ℝ in Ioi 0, contour frequency) ≤
      coefficient * (∫ frequency : ℝ in Ioi 0,
        actualBoxQuadratureIntegrand parameters box
          (sparseProfileFourthMoment a) frequency) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hcontourInt.integrableOn
      (hactualInt.const_mul coefficient).integrableOn measurableSet_Ioi
      (fun frequency _ ↦ hpointwise frequency)
  have hevent :
      (eventProbability (sparseRademacherMatrix parameters.rows d)
        (fun J ↦ (parameters.threshold : ℝ) <
          realProjectionSqNorm a J)).toReal ≤
        2 * coefficient * (∫ frequency : ℝ in Ioi 0,
          actualBoxQuadratureIntegrand parameters box
            (sparseProfileFourthMoment a) frequency) := by
    calc
      _ ≤ 2 * (∫ frequency : ℝ in Ioi 0, contour frequency) := by
        simpa only [contour] using hcontour
      _ ≤ 2 * (coefficient * (∫ frequency : ℝ in Ioi 0,
          actualBoxQuadratureIntegrand parameters box
            (sparseProfileFourthMoment a) frequency)) :=
        mul_le_mul_of_nonneg_left hintegral (by norm_num)
      _ = _ := by ring
  have hpow := inverseSqrtPow_eq_halfPower facts.rows_even hlamOne
  calc
    scaledUpperTailProbability parameters a ≤
        (2 ^ parameters.securityBits : ℝ) *
          (2 * coefficient * (∫ frequency : ℝ in Ioi 0,
            actualBoxQuadratureIntegrand parameters box
              (sparseProfileFourthMoment a) frequency)) :=
      mul_le_mul_of_nonneg_left hevent (by positivity)
    _ = boxActualPrefactorValue parameters box *
        (∫ frequency : ℝ in Ioi 0,
          actualBoxQuadratureIntegrand parameters box
            (sparseProfileFourthMoment a) frequency) := by
      unfold boxActualPrefactorValue
      dsimp only [coefficient]
      rw [hpow]
      push_cast
      ring

/-- A semantic segmented-quadrature witness for one concrete profile.  The
surrogate is normally the sum of the generated chunk rectangles and the
checked Gaussian tail. -/
structure LowProfileQuadratureWitness
    (parameters : Parameters) (box : ProfileBox) (profile : ℝ) where
  surrogate : ℝ
  surrogate_nonneg : 0 ≤ surrogate
  integral_le :
    (∫ frequency : ℝ in Ioi 0,
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
      surrogate
  integral_contains : (boxIntegral parameters box).Contains surrogate

/-- Per-box segmented enclosure.  Exact geometry is stored once, while the
profile-dependent witness supplies the analytic integral domination. -/
structure SegmentedQuadratureEnclosure
    (parameters : Parameters) (box : ProfileBox) where
  geometry : SegmentGeometry box
  witness : ∀ profile : ℝ,
    profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
    LowProfileQuadratureWitness parameters box profile

/-- The cellwise enclosure for a planned chunk is exactly the chunk enclosure
needed by the box-level fold. -/
theorem boxChunkValue_contains_rectangleChunk
    {parameters : Parameters} {box : ProfileBox} {chunk : Chunk}
    (hcell : ∀ offset, offset < chunk.count →
      (gaussianCell parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)).Contains
      (gaussianCellRectangleValue parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset))) :
    (boxChunkValue parameters box chunk).Contains
      (boxRectangleChunkValue parameters box chunk) := by
  unfold boxChunkValue boxRectangleChunkValue
  exact segmentChunk_contains_rectangleChunk hcell

/-- Construct the complete per-box enclosure from one quantified cell proof,
one quantified cap proof, and the analytic finite-plus-tail domination.  Every
argument is O(boxes); the quantified cell proof can itself be discharged by a
grouped Boolean shard and `gaussianCell_contains_rectangle`. -/
noncomputable def segmentedQuadratureEnclosure_of_cells
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (hgeometry : SegmentGeometry box)
    (hcoverage : boxChunkCells box = boxSegmentCells box)
    (hcell : ∀ chunk ∈ boxChunkPlan box, ∀ offset,
      offset < chunk.count →
      (gaussianCell parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)).Contains
      (gaussianCellRectangleValue parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)))
    (hcap : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper parameters.precision box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))))
    (hrow : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      ∀ segment ∈ box.segments, ∀ index < segment.count,
      ∀ frequency ∈ Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index) :
    SegmentedQuadratureEnclosure parameters box where
  geometry := hgeometry
  witness profile hprofile := by
    have hprofileNonneg : 0 ≤ profile := by
      have hleft : (0 : ℝ) ≤ box.profileLeft := by
        exact_mod_cast facts.profileLeft_nonneg
      exact hleft.trans hprofile.1
    have hintegral := integral_Ioi_zero_actualBoxQuadratureIntegrand_le
      facts hgeometry hcoverage hprofileNonneg (hrow profile hprofile)
    have hintegralNonneg : 0 ≤
        (∫ frequency : ℝ in Ioi 0,
          actualBoxQuadratureIntegrand parameters box profile frequency) := by
      apply setIntegral_nonneg measurableSet_Ioi
      intro frequency _
      exact actualBoxQuadratureIntegrand_nonneg facts hprofileNonneg frequency
    exact
      { surrogate := boxRectangleChunksValue parameters box +
        boxTailValue parameters box profile
        surrogate_nonneg := hintegralNonneg.trans hintegral
        integral_le := hintegral
        integral_contains := by
          apply boxIntegral_contains_rectangleChunks_add_tail
          · intro chunk hchunk
            exact boxChunkValue_contains_rectangleChunk
              (hcell chunk hchunk)
          · exact hcap profile hprofile }

/-- The generic contour reduction and one per-box segmented enclosure imply
the exact `lowSound` contract consumed by `CheckedCertificate`. -/
theorem lowProfileBoxSound_of_segmentedQuadrature
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (quadrature : SegmentedQuadratureEnclosure parameters box) :
    LowProfileBoxSound parameters box := by
  intro d a hnorm hprofile
  let profile := sparseProfileFourthMoment a
  let integralValue := ∫ frequency : ℝ in Ioi 0,
    actualBoxQuadratureIntegrand parameters box profile frequency
  let witness := quadrature.witness profile hprofile
  have hprofileNonneg : 0 ≤ profile := by
    have hleft : (0 : ℝ) ≤ box.profileLeft := by
      exact_mod_cast facts.profileLeft_nonneg
    exact hleft.trans hprofile.1
  have hintegralNonneg : 0 ≤ integralValue := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    exact actualBoxQuadratureIntegrand_nonneg facts hprofileNonneg frequency
  have hprefactorLe := boxActualPrefactorValue_le_rationalValue facts
  have hrationalNonneg :
      0 ≤ boxRationalPrefactorValue parameters box := by
    have hlamDiff : (0 : ℚ) < 1 - box.lam := sub_pos.mpr facts.lam_lt_one
    have hphi : (0 : ℚ) < UpperContourKernel.phiLower box.theta := facts.phi_pos
    unfold boxRationalPrefactorValue
    dsimp only
    positivity
  have hproduct :
      boxActualPrefactorValue parameters box * integralValue ≤
        boxRationalPrefactorValue parameters box * witness.surrogate :=
    mul_le_mul hprefactorLe witness.integral_le hintegralNonneg
      hrationalNonneg
  have hprefactorContains := boxPrefactor_contains_rationalValue facts
  have hbound : (boxBound parameters box).Contains
      (boxRationalPrefactorValue parameters box * witness.surrogate) := by
    simpa only [boxBound] using
      Interval.contains_mul hprefactorContains witness.integral_contains
  calc
    scaledUpperTailProbability parameters a ≤
        boxActualPrefactorValue parameters box * integralValue := by
      simpa only [profile, integralValue] using
        scaledUpperTailProbability_le_actualBoxEndpoint facts a hnorm hprofile
    _ ≤ boxRationalPrefactorValue parameters box * witness.surrogate := hproduct
    _ ≤ ((boxBound parameters box).upperRat : ℝ) := by
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hbound.2

/-- Convenience constructor for generated instances: replay the compact
geometry Boolean once, then provide only the profile-parametric enclosure. -/
theorem lowProfileBoxSound_of_segmentedQuadratureCheck
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (hgeometry : segmentGeometryCheck box = true)
    (witness : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      LowProfileQuadratureWitness parameters box profile) :
    LowProfileBoxSound parameters box :=
  lowProfileBoxSound_of_segmentedQuadrature facts
    ⟨segmentGeometryCheck_sound hgeometry, witness⟩

/-- End-to-end generated-instance constructor with no opaque witness field. -/
theorem lowProfileBoxSound_of_segmentedCells
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (hgeometry : segmentGeometryCheck box = true)
    (hcoverage : boxChunkCoverageCheck box = true)
    (hcell : ∀ chunk ∈ boxChunkPlan box, ∀ offset,
      offset < chunk.count →
      (gaussianCell parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)).Contains
      (gaussianCellRectangleValue parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)))
    (hcap : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper parameters.precision box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))))
    (hrow : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      ∀ segment ∈ box.segments, ∀ index < segment.count,
      ∀ frequency ∈ Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index) :
    LowProfileBoxSound parameters box :=
  lowProfileBoxSound_of_segmentedQuadrature facts
    (segmentedQuadratureEnclosure_of_cells
      facts (segmentGeometryCheck_sound hgeometry)
      (boxChunkCoverageCheck_sound hcoverage) hcell hcap hrow)

/-- Fully executable generated-box entry point.  Concrete modules replay four
small box-level checks and prove only the profile-parametric real-cap
containment; all cell enclosure and row-majorant obligations are derived here. -/
theorem lowProfileBoxSound_of_checks
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    (hgeometry : segmentGeometryCheck box = true)
    (hcoverage : boxChunkCoverageCheck box = true)
    (hbase : rowExpressionBaseCheck parameters box = true)
    (hlambdaBase : lambdaSquareBaseCheck parameters box = true)
    (hcap : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper parameters.precision box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    LowProfileBoxSound parameters box := by
  have geometry := segmentGeometryCheck_sound hgeometry
  have coverage := boxChunkCoverageCheck_sound hcoverage
  exact lowProfileBoxSound_of_segmentedCells facts hgeometry hcoverage
    (boxGaussianCellsContainRectangles_of_facts facts geometry coverage
      hbase hlambdaBase hcap) hcap
    (boxRowMajorant_of_geometry_and_baseCheck facts geometry hbase hcap)

/-- Literal security-scaled real-axis endpoint for the high-profile branch. -/
noncomputable def highProfileScaledEndpoint
    (parameters : Parameters) (box : HighProfileBox) (profile : ℝ) : ℝ :=
  (2 ^ parameters.securityBits : ℝ) *
    Real.exp (-((box.lam * parameters.threshold : ℚ) : ℝ)) *
    (((1 / (1 - box.lam) ^ (parameters.rows / 2) : ℚ) : ℝ)) *
    realRowDeficitCap
      (Real.sqrt profile * (box.lam : ℝ) /
        (1 - (box.lam : ℝ))) ^ parameters.rows

/-- The executable high-profile endpoint contains its literal analytic value. -/
theorem highProfileBound_contains_scaledEndpoint
    {parameters : Parameters} {box : HighProfileBox}
    (facts : HighProfileFacts parameters box)
    {profile : ℝ} (hprofile : (box.profileMinimum : ℝ) ≤ profile) :
    (highProfileBound parameters box).Contains
      (highProfileScaledEndpoint parameters box profile) := by
  have hcap := facts.capContains profile hprofile
  have hscaledExponential := UpperContourKernel.scaledNegExpUpper_contains
    parameters.precision parameters.securityBlockBits
      (box.lam * parameters.threshold) 34
      parameters.securityScaleSquarings facts.exponent_nonneg
  have hgaussian := Interval.contains_ofRat parameters.precision
    (1 / (1 - box.lam) ^ (parameters.rows / 2) : ℚ)
  have hcapPower := UpperContourKernel.tensorPower_contains hcap
    parameters.rowOddPart parameters.rowSquareCount
  have hproduct := Interval.contains_mul
    (Interval.contains_mul hscaledExponential hgaussian) hcapPower
  simpa [highProfileBound, highProfileScaledEndpoint, Parameters.rows,
    Parameters.securityBits, UpperContourKernel.frac] using hproduct

/-- Generic high-profile Chernoff/real-deficit bridge. -/
theorem highProfileBoxSound_of_facts
    {parameters : Parameters} {box : HighProfileBox}
    (facts : HighProfileFacts parameters box) :
    HighProfileBoxSound parameters box := by
  intro d a hnorm hprofile
  have hlam0 : (0 : ℝ) ≤ box.lam := by exact_mod_cast facts.lam_nonneg
  have hlam1 : (box.lam : ℝ) < 1 := by exact_mod_cast facts.lam_lt_one
  have hprob :=
    sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit_at_profileLeft
      (m := parameters.rows) a (threshold := (parameters.threshold : ℝ))
      (lambda := (box.lam : ℝ))
      (profileLeft := (box.profileMinimum : ℝ))
      hlam0 hlam1 hnorm hprofile
  have hprob' :
      (eventProbability (sparseRademacherMatrix parameters.rows d)
        (fun J ↦ (parameters.threshold : ℝ) <
          realProjectionSqNorm a J)).toReal ≤
        Real.exp (-((box.lam : ℝ) * (parameters.threshold : ℝ))) *
          ((1 / Real.sqrt (1 - (box.lam : ℝ))) *
            realRowDeficitCap
              (Real.sqrt (box.profileMinimum : ℝ) * (box.lam : ℝ) /
                (1 - (box.lam : ℝ)))) ^ parameters.rows := by
    simpa only [neg_mul] using hprob
  have hpow := inverseSqrtPow_eq_halfPower facts.rows_even hlam1
  have hscaled : scaledUpperTailProbability parameters a ≤
      highProfileScaledEndpoint parameters box
        (box.profileMinimum : ℝ) := by
    calc
      scaledUpperTailProbability parameters a ≤
          (2 ^ parameters.securityBits : ℝ) *
            (Real.exp (-((box.lam : ℝ) *
                (parameters.threshold : ℝ))) *
              ((1 / Real.sqrt (1 - (box.lam : ℝ))) *
                realRowDeficitCap
                  (Real.sqrt (box.profileMinimum : ℝ) *
                    (box.lam : ℝ) / (1 - (box.lam : ℝ)))) ^
                parameters.rows) :=
        mul_le_mul_of_nonneg_left hprob' (by positivity)
      _ = highProfileScaledEndpoint parameters box
          (box.profileMinimum : ℝ) := by
        rw [mul_pow, hpow]
        unfold highProfileScaledEndpoint
        push_cast
        ring
  have hcontains := highProfileBound_contains_scaledEndpoint facts
    (profile := (box.profileMinimum : ℝ)) le_rfl
  exact hscaled.trans (by
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2)

end CertifiedJL.SparseUpperContourFamily
