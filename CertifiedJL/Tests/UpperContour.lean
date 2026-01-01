/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContour
import Lean.Util.CollectAxioms

/-! Producer-direct canaries for the sparse upper-tail contour assembly. -/

open MeasureTheory ProbabilityTheory

namespace CertifiedJL.Tests.UpperContour

/-- A concrete Gaussian pins the generic bilateral factor `2`. -/
example :
    (∫ u : ℝ, Real.exp (-(1 : ℝ) * u ^ 2)) =
      2 * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(1 : ℝ) * u ^ 2) := by
  apply integral_eq_two_mul_integral_Ioi_of_even
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))
  intro u
  simp only [neg_sq]

/-- Fixed nontrivial contour parameters directly consume integrability. -/
example {d : ℕ} (a : Fin d → ℝ) :
    Integrable (fun u : ℝ =>
      ‖shiftedGaussianContourWeight (3 / 2) (2 / 5) 338 (1 / 2) u‖ *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure ((1 / 2 : ℝ) + u * Complex.I) ^ 3‖) :=
  integrable_sparseUpperContourNorm a 3 (by norm_num) (by norm_num)

/-- Two actual sparse rows produce the square of the one-row quadratic MGF. -/
example {d : ℕ} (a : Fin d → ℝ) (s : ℂ) :
    complexMGF (realProjectionSqNorm (m := 2) a)
        (sparseRademacherMatrix 2 d).toMeasure s =
      quadraticComplexMGF
        (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure s ^ 2 :=
  complexMGF_realProjectionSqNorm_eq_pow a s

/-- The public contour producer keeps the strict threshold and powered row MGF. -/
example {m d : ℕ} (a : Fin d → ℝ)
    {sigma theta t lambda : ℝ}
    (hsigma : 0 < sigma) (hlambda : 0 < lambda) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => t < realProjectionSqNorm a J)).toReal ≤
      ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖ :=
  sparseRademacherMatrix_realProjectionSqNorm_toReal_le_contour a hsigma hlambda

/-- The contour norm is reduced to the exact positive-frequency integral. -/
example {m d : ℕ} (a : Fin d → ℝ)
    {sigma theta t lambda : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    (∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
      ‖quadraticComplexMGF
        (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖) =
      2 * ∫ u in Set.Ioi (0 : ℝ),
        ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖ :=
  integral_sparseUpperContourNorm_eq_two_mul_Ioi a m hlambda hsigma

/-- The certificate-facing producer has no residual whole-line integral. -/
example {m d : ℕ} (a : Fin d → ℝ)
    {sigma theta t lambda : ℝ}
    (hsigma : 0 < sigma) (hlambda : 0 < lambda) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => t < realProjectionSqNorm a J)).toReal ≤
      2 * ∫ u in Set.Ioi (0 : ℝ),
        ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖ :=
  sparseRademacherMatrix_realProjectionSqNorm_toReal_le_positiveContour
    a hsigma hlambda

/-- A nonzero frequency directly pins the even U10 contour weight. -/
example (sigma theta t lambda : ℝ) :
    ‖shiftedGaussianContourWeight sigma theta t lambda (-3)‖ =
      ‖shiftedGaussianContourWeight sigma theta t lambda 3‖ :=
  norm_shiftedGaussianContourWeight_neg sigma theta t lambda 3

/-- The normalized fourth-order producer keeps both derivative errors distinct. -/
example {M : ℂ} {profile lambda frequency : ℝ}
    (herror :
      ‖M - (1 - (lambda + frequency * Complex.I)) ^ (-1 / 2 : ℂ) +
          ((profile / 8 : ℝ) : ℂ) *
            (lambda + frequency * Complex.I) ^ 2 *
            (1 - (lambda + frequency * Complex.I)) ^ (-5 / 2 : ℂ)‖ ≤
        profile ^ 2 / 9216 *
            quadraticExpDerivativeMajorant 8
              ‖lambda + frequency * Complex.I‖ lambda +
          11 * (profile * Real.sqrt profile) / 5760 *
            quadraticExpDerivativeMajorant 6
              ‖lambda + frequency * Complex.I‖ lambda) :
    Real.sqrt (1 - lambda) * ‖M‖ ≤
      sparseUpperFourthOrderNormalizedMajorant profile lambda frequency :=
  normalized_rowMGF_le_fourthOrderMajorant_of_error herror

/-- A profile-left U8 consumer pins the antitone endpoint direction. -/
example {m d : ℕ} (a : Fin d → ℝ) {threshold lambda profileLeft : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : profileLeft ≤ sparseProfileFourthMoment a) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => threshold < realProjectionSqNorm a J)).toReal ≤
      Real.exp (-lambda * threshold) *
        ((1 / Real.sqrt (1 - lambda)) *
          realRowDeficitCap
            (Real.sqrt profileLeft * lambda / (1 - lambda))) ^ m :=
  sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit_at_profileLeft
    a hlambda0 hlambda1 hnorm hprofile

run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.complexMGF_realProjectionSqNorm_eq_pow,
      ``CertifiedJL.sparseRademacherMatrix_realProjectionSqNorm_toReal_le_contour,
      ``CertifiedJL.normalized_rowMGF_le_fourthOrderMajorant_of_error,
      ``CertifiedJL.normalized_rowMGF_le_realDeficit,
      ``CertifiedJL.normalized_rowMGF_le_contourRowMajorant,
      ``CertifiedJL.integral_eq_two_mul_integral_Ioi_of_even,
      ``CertifiedJL.norm_shiftedGaussianContourWeight_neg,
      ``CertifiedJL.integrable_sparseUpperContourNorm,
      ``CertifiedJL.integral_sparseUpperContourNorm_eq_two_mul_Ioi,
      ``CertifiedJL.sparseRademacherMatrix_realProjectionSqNorm_toReal_le_positiveContour,
      ``CertifiedJL.sparseRademacherMatrix_realProjectionSqNorm_toReal_le_chernoff,
      ``CertifiedJL.sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit,
      ``CertifiedJL.sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit_at_profileLeft]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperContour
