import CertifiedJL.Analysis.Peano.PeanoKStopLossMoments

open MeasureTheory Set
open ProbabilityTheory

namespace CertifiedJL.Tests.PeanoKLaw

example : peanoKDensity 0 = 2 *
    cubicStopLossDifference (gaussianReal 0 1)
      standardRademacherMeasure 0 := by
  rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]

example : peanoKDensity 1 =
    2 * ∫ y in Ioi (1 : ℝ), (y - 1) ^ 3 ∂(gaussianReal 0 1) := by
  exact peanoKDensity_of_one_le (by norm_num)

example : peanoKDensity (-1) =
    2 * ∫ y in Iio (-1 : ℝ), (-1 - y) ^ 3 ∂(gaussianReal 0 1) := by
  exact peanoKDensity_of_le_neg_one (by norm_num)

example : 0 ≤ peanoKDensity 2 :=
  peanoKDensity_nonneg_of_one_le (by norm_num)

example : 0 ≤ peanoKDensity (-2) :=
  peanoKDensity_nonneg_of_le_neg_one (by norm_num)

example : Integrable (fun t : ℝ => |t| ^ 4 * |peanoKDensity t|) volume :=
  integrable_absPow_mul_abs_peanoKDensity 4

example : peanoKDensity (-((3 : ℝ) / 5)) = peanoKDensity (3 / 5) := by
  exact peanoKDensity_neg (3 / 5)

example : 0 ≤ peanoKDensity (3 / 5) := peanoKDensity_nonneg (3 / 5)

example : 0 ≤ peanoKDensity (-((4 : ℝ) / 7)) :=
  peanoKDensity_nonneg (-((4 : ℝ) / 7))

/- The asymmetric threshold pins the nonzero branch and the exact glue point
of the squared positive-part cubic. -/
example : ConvexOn ℝ (Ici 0) (peanoCubicSquareProfile (3 / 5)) :=
  convexOn_peanoCubicSquareProfile (by norm_num)

example : peanoCubicSquareProfile (3 / 5) ((3 / 5) ^ 2) = 0 := by
  norm_num [peanoCubicSquareProfile]

example : peanoCubicSquareProfile (3 / 5) 1 = (2 / 5) ^ 3 := by
  norm_num [peanoCubicSquareProfile]

/- Exact normalization and a low even moment pin both beta denominators and
the standard-Gaussian scaling used by the general moment theorem. -/
example : (∫ t : ℝ, peanoKDensity t) = 1 := integral_peanoKDensity

example : (∫ t : ℝ, |t| ^ 2 * peanoKDensity t) = 7 / 15 := by
  have h := integral_abs_evenPow_mul_peanoKDensity 1
  norm_num [peanoBetaCoeff] at h ⊢
  exact h

/- The two odd absolute moments consumed by U6 remain explicit instances of
the same Tonelli/beta identity, rather than separately axiomatized bounds. -/
example : (∫ t : ℝ, |t| ^ 11 * peanoKDensity t) =
    4 * peanoBetaCoeff 11 *
      ((∫ y, (max y 0) ^ 15 ∂(gaussianReal 0 1)) - 1 / 2) :=
  integral_absPow_mul_peanoKDensity 11

example : (∫ t : ℝ, |t| ^ 15 * peanoKDensity t) =
    4 * peanoBetaCoeff 15 *
      ((∫ y, (max y 0) ^ 19 ∂(gaussianReal 0 1)) - 1 / 2) :=
  integral_absPow_mul_peanoKDensity 15

example : (∫ t : ℝ, |t| ^ 11 * peanoKDensity t) =
    (645120 / Real.sqrt (2 * Real.pi) - 1 / 2) / 1365 :=
  integral_abs_pow_eleven_mul_peanoKDensity

example : (∫ t : ℝ, |t| ^ 15 * peanoKDensity t) =
    (185794560 / Real.sqrt (2 * Real.pi) - 1 / 2) / 3876 :=
  integral_abs_pow_fifteen_mul_peanoKDensity

example : IsProbabilityMeasure peanoKMeasure := inferInstance

example : peanoKMeasure.map (fun x : ℝ => -x) = peanoKMeasure :=
  peanoKMeasure_map_neg

example : Integrable (fun x : ℝ => |x| ^ 15) peanoKMeasure :=
  integrable_absPow_peanoKMeasure 15

example : (∫ x : ℝ, |x| ^ 11 ∂peanoKMeasure) =
    (645120 / Real.sqrt (2 * Real.pi) - 1 / 2) / 1365 := by
  rw [integral_absPow_peanoKMeasure,
    integral_abs_pow_eleven_mul_peanoKDensity]

example : (∫ x : ℝ, |x| ^ 15 ∂peanoKMeasure) =
    (185794560 / Real.sqrt (2 * Real.pi) - 1 / 2) / 3876 := by
  rw [integral_absPow_peanoKMeasure,
    integral_abs_pow_fifteen_mul_peanoKDensity]

example : GaussianEvenMomentDomination peanoKMeasure 1 1 :=
  peanoK_evenMomentDomination

/- Positive asymmetric points pin the rational Mills certificate away from
the singular denominator at zero. -/
example :
    Probability.standardGaussianDensity (3 / 5) *
        ((3 / 5 : ℝ) ^ 4 + 9 * (3 / 5) ^ 2 - 2) ≤
      Probability.standardGaussianTail (3 / 5) *
        ((3 / 5 : ℝ) ^ 5 + 10 * (3 / 5) ^ 3 + 5 * (3 / 5)) :=
  standardGaussian_rational_mills_lower (by norm_num)

example :
    Probability.standardGaussianDensity 1 * (1 ^ 4 + 9 * 1 ^ 2 - 2) ≤
      Probability.standardGaussianTail 1 * (1 ^ 5 + 10 * 1 ^ 3 + 5 * 1) :=
  standardGaussian_rational_mills_lower (by norm_num)

/- U6a canaries pin the exact nested fifth-stop-loss coefficient, the
positive-half-line closed form, reflection, and global sign. -/
example :
    firstStopLossDifference (gaussianReal 0 1) peanoKMeasure (3 / 5) =
      (2 - 9 * (3 / 5 : ℝ) ^ 2 - (3 / 5) ^ 4) / 10 *
          Probability.standardGaussianDensity (3 / 5) +
        ((3 / 5 : ℝ) ^ 5 + 10 * (3 / 5) ^ 3 + 5 * (3 / 5)) / 10 *
          Probability.standardGaussianTail (3 / 5) +
        (max (1 - (3 / 5 : ℝ)) 0) ^ 5 / 20 :=
  firstStopLossDifference_standardGaussian_peanoKMeasure_of_nonneg (by norm_num)

example :
    firstStopLossDifference (gaussianReal 0 1) peanoKMeasure (-3 / 5) =
      firstStopLossDifference (gaussianReal 0 1) peanoKMeasure (3 / 5) := by
  simpa only [neg_div] using
    firstStopLossDifference_standardGaussian_peanoKMeasure_neg (3 / 5)

example : 0 ≤ firstStopLossDifference (gaussianReal 0 1) peanoKMeasure 0 :=
  firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg 0

example : 0 ≤ firstStopLossDifference (gaussianReal 0 1) peanoKMeasure (-4 / 7) :=
  firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg (-4 / 7)

example : PositiveStopLossMomentDomination
    (gaussianReal 0 1) peanoKMeasure (11 / 15) :=
  peanoK_positiveStopLossMomentDomination

example : peanoKStopLossMeasure.map (fun x : ℝ => -x) =
    peanoKStopLossMeasure := peanoKStopLossMeasure_map_neg

example : Integrable (fun x : ℝ => |x| ^ 15) peanoKStopLossMeasure :=
  integrable_absPow_peanoKStopLossMeasure 15

example (ell : ℕ) :
    (∫ t : ℝ, |t| ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) ≤
      (11 / 15 : ℝ) * centeredGaussianEvenMoment 1 ell :=
  integral_abs_evenPow_mul_firstStopLossDifference_le_eleven_fifteenths ell

example {ρ : Measure ℝ} {varianceW : NNReal}
    (s : ℂ) (c : ℝ)
    (hlifted :
      (∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂(gaussianReal 0 1) ∂ρ) -
          ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
            ∂peanoKMeasure ∂ρ =
        c ^ 2 • ∫ w, ∫ t,
          firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
            iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ)
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hvariance : varianceW + scaledVariance c 1 ≤ (2 : NNReal)⁻¹)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    ‖(∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂(gaussianReal 0 1) ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂peanoKMeasure ∂ρ‖ ≤
      (11 / 15 : ℝ) * c ^ 2 *
        quadraticExpDerivativeMajorant 6 ‖s‖ s.re :=
  norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le
    s c hlifted hW hvariance hs_nonneg hs_lt_one

#print axioms peanoKDensity_eq_two_mul_cubicStopLossDifference
#print axioms integrable_absPow_mul_abs_peanoKDensity
#print axioms peanoKDensity_neg
#print axioms peanoKDensity_nonneg_of_one_le
#print axioms peanoKDensity_nonneg_of_le_neg_one
#print axioms convexOn_peanoCubicSquareProfile
#print axioms peanoKDensity_nonneg
#print axioms integral_Ici_absPow_mul_cubicStopLoss
#print axioms integral_absPow_mul_peanoKDensity
#print axioms integral_abs_evenPow_mul_peanoKDensity
#print axioms integral_peanoKDensity
#print axioms integral_standardGaussian_max_oddPow
#print axioms integral_abs_pow_eleven_mul_peanoKDensity
#print axioms integral_abs_pow_fifteen_mul_peanoKDensity
#print axioms peanoKMeasure
#print axioms peanoKMeasure_map_neg
#print axioms integral_abs_evenPow_peanoKMeasure
#print axioms peanoK_evenMomentDomination
#print axioms standardGaussian_rational_mills_lower
#print axioms firstStopLossDifference_standardGaussian_peanoKMeasure_eq_fifth
#print axioms integral_standardGaussian_fifth_stopLoss
#print axioms firstStopLossDifference_standardGaussian_peanoKMeasure_of_nonneg
#print axioms firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg
#print axioms integral_abs_evenPow_mul_firstStopLossDifference
#print axioms peanoK_positiveStopLossMomentDomination
#print axioms norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le

run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.peanoKDensity_eq_two_mul_cubicStopLossDifference,
      ``CertifiedJL.integrable_absPow_mul_abs_peanoKDensity,
      ``CertifiedJL.peanoKDensity_neg,
      ``CertifiedJL.peanoKDensity_nonneg,
      ``CertifiedJL.integral_Ici_absPow_mul_cubicStopLoss,
      ``CertifiedJL.integral_absPow_mul_peanoKDensity,
      ``CertifiedJL.integral_abs_evenPow_mul_peanoKDensity,
      ``CertifiedJL.integral_peanoKDensity,
      ``CertifiedJL.integral_abs_pow_eleven_mul_peanoKDensity,
      ``CertifiedJL.integral_abs_pow_fifteen_mul_peanoKDensity,
      ``CertifiedJL.peanoKMeasure,
      ``CertifiedJL.peanoKMeasure_map_neg,
      ``CertifiedJL.integral_abs_evenPow_peanoKMeasure,
      ``CertifiedJL.peanoK_evenMomentDomination,
      ``CertifiedJL.standardGaussian_rational_mills_lower,
      ``CertifiedJL.firstStopLossDifference_standardGaussian_peanoKMeasure_eq_fifth,
      ``CertifiedJL.integral_standardGaussian_fifth_stopLoss,
      ``CertifiedJL.integral_standardRademacher_fifth_stopLoss,
      ``CertifiedJL.firstStopLossDifference_standardGaussian_peanoKMeasure_of_nonneg,
      ``CertifiedJL.firstStopLossDifference_standardGaussian_peanoKMeasure_neg,
      ``CertifiedJL.firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg,
      ``CertifiedJL.integral_abs_evenPow_mul_firstStopLossDifference,
      ``CertifiedJL.integral_abs_evenPow_mul_firstStopLossDifference_le_eleven_fifteenths,
      ``CertifiedJL.peanoKStopLossMeasure,
      ``CertifiedJL.peanoKStopLossMeasure_map_neg,
      ``CertifiedJL.peanoK_positiveStopLossMomentDomination,
      ``CertifiedJL.norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.PeanoKLaw
