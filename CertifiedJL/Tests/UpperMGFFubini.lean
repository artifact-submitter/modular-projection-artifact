/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.ShiftedGaussianInversion
import Lean.Util.CollectAxioms

/-! Direct mutation canaries for the iid quadratic MGF and contour boundary. -/

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace CertifiedJL.Tests.UpperMGFFubini

/-- Tensorization has the correct empty-product behavior. -/
example {Omega Omega0 : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega0]
    {mu : Measure Omega} {mu0 : Measure Omega0}
    (Z : Fin 0 → Omega → ℝ) (Z0 : Omega0 → ℝ)
    (hIndep : iIndepFun Z mu)
    (hIdent : ∀ i, IdentDistrib (Z i) Z0 mu mu0) (s : ℂ) :
    complexMGF (fun omega => ∑ i, (Z i omega) ^ 2) mu s = 1 := by
  simpa using complexMGF_sum_sq_eq_quadraticComplexMGF_pow
    Z Z0 hIndep hIdent s

/-- Tensorization has no spurious factor in the one-coordinate case. -/
example {Omega Omega0 : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega0]
    {mu : Measure Omega} {mu0 : Measure Omega0}
    (Z : Fin 1 → Omega → ℝ) (Z0 : Omega0 → ℝ)
    (hIndep : iIndepFun Z mu)
    (hIdent : ∀ i, IdentDistrib (Z i) Z0 mu mu0) (s : ℂ) :
    complexMGF (fun omega => ∑ i, (Z i omega) ^ 2) mu s =
      quadraticComplexMGF Z0 mu0 s := by
  simpa using complexMGF_sum_sq_eq_quadraticComplexMGF_pow
    Z Z0 hIndep hIdent s

/-- An asymmetric two-coordinate consumer pins the square on the power. -/
example {Omega Omega0 : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega0]
    {mu : Measure Omega} {mu0 : Measure Omega0}
    (Z : Fin 2 → Omega → ℝ) (Z0 : Omega0 → ℝ)
    (hIndep : iIndepFun Z mu)
    (hIdent : ∀ i, IdentDistrib (Z i) Z0 mu mu0) (s : ℂ) :
    complexMGF (fun omega => ∑ i, (Z i omega) ^ 2) mu s =
      quadraticComplexMGF Z0 mu0 s ^ 2 :=
  complexMGF_sum_sq_eq_quadraticComplexMGF_pow Z Z0 hIndep hIdent s

/-- The negative-frequency side is the conjugate, with the sign exposed. -/
example {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (lambda u : ℝ) :
    quadraticComplexMGF Z mu (lambda + (-u) * Complex.I) =
      conj (quadraticComplexMGF Z mu (lambda + u * Complex.I)) := by
  convert quadraticComplexMGF_vertical_conj Z mu lambda u using 1
  ring_nf

/-- Pairing uses the powered MGF and preserves the negative sign. -/
example {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (lambda u : ℝ) (m : ℕ) :
    ‖quadraticComplexMGF Z mu (lambda + (-u) * Complex.I) ^ m‖ =
      ‖quadraticComplexMGF Z mu (lambda + u * Complex.I) ^ m‖ := by
  convert norm_quadraticComplexMGF_pow_neg_eq Z mu lambda u m using 1
  ring_nf

/-- An asymmetric direct consumer pins every premise of the Fubini boundary. -/
example {Omega U : Type*} [MeasurableSpace Omega] [MeasurableSpace U]
    {mu : Measure Omega} {nu : Measure U} [SFinite mu] [SFinite nu]
    (X : Omega → ℝ) (H : ℝ → ℝ) (W : U → ℂ) (v : U → ℝ) (lambda : ℝ)
    (hX : Measurable X) (hW : Integrable W nu) (hv : Measurable v)
    (hReal : Integrable (fun omega => Real.exp (lambda * X omega)) mu)
    (hRepresentation : ∀ x,
      (H x : ℂ) = ∫ u, W u *
        Complex.exp ((lambda + v u * Complex.I) * x) ∂nu) :
    (∫ omega, H (X omega) ∂mu) ≤
      ∫ u, ‖W u‖ * ‖complexMGF X mu
        (lambda + v u * Complex.I)‖ ∂nu :=
  integral_comp_le_integral_norm_complexMGF_of_contourRepresentation
    X H W v lambda hX hW hv hReal hRepresentation

/-- The exact U10a specialization exposes the contour identity as its only
contour-owned premise. -/
example {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [SFinite mu]
    (X : Omega → ℝ) {sigma theta t lambda : ℝ}
    (hX : Measurable X)
    (hWeight : Integrable
      (shiftedGaussianContourWeight sigma theta t lambda) volume)
    (hReal : Integrable (fun omega => Real.exp (lambda * X omega)) mu)
    (hRepresentation : ∀ x,
      (shiftedGaussianSmoothing sigma theta t x : ℂ) =
        ∫ u : ℝ, shiftedGaussianContourWeight sigma theta t lambda u *
          Complex.exp ((lambda + u * Complex.I) * x)) :
    (∫ omega, shiftedGaussianSmoothing sigma theta t (X omega) ∂mu) ≤
      ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖complexMGF X mu (lambda + u * Complex.I)‖ :=
  integral_shiftedGaussianSmoothing_le_contour
    X hX hWeight hReal hRepresentation

/-- The contour-owned integrability premise is discharged at non-unit scale. -/
example : Integrable
    (shiftedGaussianContourWeight (3 / 2) (-2) 7 (1 / 3)) := by
  exact integrable_shiftedGaussianContourWeight (by norm_num) (by norm_num)

/-- The exact representation is consumed away from the threshold. -/
example :
    (shiftedGaussianSmoothing (3 / 2) (-2) 7 (-5) : ℂ) =
      ∫ u : ℝ, shiftedGaussianContourWeight (3 / 2) (-2) 7 (1 / 3) u *
        Complex.exp (((1 / 3 : ℝ) + u * Complex.I) * (-5 : ℝ)) := by
  exact shiftedGaussianSmoothing_contourRepresentation
    (by norm_num) (by norm_num) (-5)

run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.complexMGF_sum_sq_eq_quadraticComplexMGF_pow,
      ``CertifiedJL.integrable_quadraticCexp_vertical_of_integrable_real,
      ``CertifiedJL.quadraticComplexMGF_vertical_conj,
      ``CertifiedJL.norm_quadraticComplexMGF_pow_neg_eq,
      ``CertifiedJL.integrable_shiftedGaussianContourWeight,
      ``CertifiedJL.shiftedGaussianSmoothing_contourRepresentation,
      ``CertifiedJL.integral_comp_le_integral_norm_complexMGF_of_contourRepresentation,
      ``CertifiedJL.integral_shiftedGaussianSmoothing_le_contour]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.all allowed.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperMGFFubini
