/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.Experiment
import CertifiedJL.Probability.Finite.UniformPiBridge
import CertifiedJL.Analysis.Gaussian.HalfGaussian
import CertifiedJL.Analysis.Gaussian.ShiftedGaussianInversion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic

/-!
# Finite iid quadratic-statistic assembly

Distribution-independent lemmas for finite iid row experiments.  These keep
the product-measure and quadratic-MGF tensorization used by both sparse and
sign Johnson--Lindenstrauss upper tails below either paper-specific model.
-/

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

namespace CertifiedJL

/-- Any real-valued function is integrable against a finite PMF. -/
theorem integrable_of_finitePMF {Omega : Type*} [Finite Omega]
    [MeasurableSpace Omega] [MeasurableSingletonClass Omega]
    (p : PMF Omega) (f : Omega → ℝ) :
    Integrable f p.toMeasure := by
  exact Integrable.of_finite

/-- The nonnegative quadratic statistic assigned to one row for an arbitrary row type and row distribution. -/
noncomputable def iidRowValueSqNorm {m : ℕ} {Row : Type*}
    (rowValue : Row → ℝ) (rows : Fin m → Row) : ℝ :=
  ∑ j, rowValue (rows j) ^ 2

/-- The quadratic MGF of iid rows factors as the exact power of the one-row
quadratic MGF. -/
theorem complexMGF_iidRowValueSqNorm_eq_pow
    {m : ℕ} {Row : Type*} [MeasurableSpace Row]
    (rowPMF : PMF Row) (rowValue : Row → ℝ) (s : ℂ) :
    complexMGF (iidRowValueSqNorm (m := m) rowValue)
        (Measure.pi (fun _ : Fin m => rowPMF.toMeasure)) s =
      quadraticComplexMGF rowValue rowPMF.toMeasure s ^ m := by
  rw [complexMGF]
  calc
    (∫ rows, Complex.exp
        (s * (iidRowValueSqNorm rowValue rows : ℂ)) ∂
          Measure.pi (fun _ : Fin m => rowPMF.toMeasure)) =
        ∫ rows, ∏ j, Complex.exp
          (s * (rowValue (rows j) : ℂ) ^ 2) ∂
            Measure.pi (fun _ : Fin m => rowPMF.toMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with rows
      rw [← Complex.exp_sum]
      congr 1
      simp only [iidRowValueSqNorm]
      push_cast
      rw [Finset.mul_sum]
    _ = ∏ _j : Fin m, ∫ row, Complex.exp
          (s * (rowValue row : ℂ) ^ 2) ∂rowPMF.toMeasure := by
      exact MeasureTheory.integral_fintype_prod_eq_prod
        (μ := fun _ : Fin m => rowPMF.toMeasure)
        (fun _ row => Complex.exp (s * (rowValue row : ℂ) ^ 2))
    _ = quadraticComplexMGF rowValue rowPMF.toMeasure s ^ m := by
      simp [quadraticComplexMGF, complexMGF]

/-- Distribution-independent Chernoff bound for a finite iid quadratic
squared norm.  Model-specific layers only need to identify their matrix distribution with
the product of the one-row distribution. -/
theorem finiteIidRowValueSqNorm_toReal_le_chernoff
    {m : ℕ} {Row : Type*} [Countable Row] [MeasurableSpace Row]
    [MeasurableSingletonClass Row]
    (rowPMF : PMF Row) (matrixPMF : PMF (Fin m → Row))
    (hpi : matrixPMF.toMeasure =
      Measure.pi (fun _ : Fin m => rowPMF.toMeasure))
    (hmatrixIntegrable : ∀ f : (Fin m → Row) → ℝ,
      Integrable f matrixPMF.toMeasure)
    (rowValue : Row → ℝ) {threshold lambda : ℝ}
    (hlambda : 0 ≤ lambda) :
    (eventProbability matrixPMF
        (fun rows => threshold < iidRowValueSqNorm rowValue rows)).toReal ≤
      Real.exp (-lambda * threshold) *
        (∫ row, Real.exp (lambda * rowValue row ^ 2) ∂rowPMF.toMeasure) ^ m := by
  let X : (Fin m → Row) → ℝ := iidRowValueSqNorm rowValue
  have hreal : Integrable (fun rows => Real.exp (lambda * X rows))
      matrixPMF.toMeasure := hmatrixIntegrable _
  rw [eventProbability_eq_toMeasure]
  calc
    matrixPMF.toMeasure.real (X ⁻¹' Set.Ioi threshold) ≤
        matrixPMF.toMeasure.real {rows | threshold ≤ X rows} := by
      apply measureReal_mono
      · intro rows hrows
        exact (show threshold < X rows from hrows).le
      · exact measure_ne_top _ _
    _ ≤ Real.exp (-lambda * threshold) *
        mgf X matrixPMF.toMeasure lambda :=
      measure_ge_le_exp_mul_mgf threshold hlambda hreal
    _ = Real.exp (-lambda * threshold) *
        (∫ row, Real.exp (lambda * rowValue row ^ 2) ∂rowPMF.toMeasure) ^ m := by
      congr 1
      rw [mgf, hpi]
      calc
        (∫ rows, Real.exp
            (lambda * iidRowValueSqNorm rowValue rows) ∂
              Measure.pi (fun _ : Fin m => rowPMF.toMeasure)) =
            ∫ rows, ∏ j, Real.exp
              (lambda * rowValue (rows j) ^ 2) ∂
                Measure.pi (fun _ : Fin m => rowPMF.toMeasure) := by
          apply integral_congr_ae
          filter_upwards [] with rows
          rw [iidRowValueSqNorm, Finset.mul_sum, Real.exp_sum]
        _ = ∏ _j : Fin m, ∫ row, Real.exp
              (lambda * rowValue row ^ 2) ∂rowPMF.toMeasure := by
          exact MeasureTheory.integral_fintype_prod_eq_prod
            (μ := fun _ : Fin m => rowPMF.toMeasure)
            (fun _ row => Real.exp (lambda * rowValue row ^ 2))
        _ = (∫ row, Real.exp (lambda * rowValue row ^ 2)
              ∂rowPMF.toMeasure) ^ m := by simp

/-- The exact U10 weight has even modulus in the contour frequency. -/
theorem norm_shiftedGaussianContourWeight_neg
    (sigma theta threshold lambda u : ℝ) :
    ‖shiftedGaussianContourWeight sigma theta threshold lambda (-u)‖ =
      ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ := by
  rw [shiftedGaussianContourWeight_eq_kernel,
    shiftedGaussianContourWeight_eq_kernel, norm_mul, norm_mul,
    norm_shiftedGaussianContourKernel, norm_shiftedGaussianContourKernel]
  congr 1
  congr 2 <;> ring

/-- Exact real factorization of the shifted-Gaussian contour weight into its
frequency-independent coefficient and positive-frequency quadrature factors. -/
theorem norm_shiftedGaussianContourWeight_eq_quadratureFactors
    (sigma theta threshold lambda frequency : ℝ) :
    ‖shiftedGaussianContourWeight sigma theta threshold lambda frequency‖ =
      (1 / (2 * Real.pi * standardGaussianCDF theta)) *
        Real.exp (-(lambda * (threshold - theta * sigma) -
          sigma ^ 2 * lambda ^ 2 / 2)) *
        Real.exp (-(sigma ^ 2 / 2) * frequency ^ 2) *
        (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)) := by
  rw [shiftedGaussianContourWeight_eq_kernel, norm_mul,
    norm_shiftedGaussianContourKernel]
  have hdenominatorNorm :
      ‖(2 : ℂ) * (Real.pi : ℂ) * (standardGaussianCDF theta : ℂ)‖ =
        2 * Real.pi * standardGaussianCDF theta := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos Real.pi_pos, abs_of_pos (standardGaussianCDF_pos theta)]
    norm_num
  rw [norm_div, norm_one, hdenominatorNorm]
  rw [show
      lambda * (-threshold + theta * sigma) +
          sigma ^ 2 * (lambda ^ 2 - frequency ^ 2) / 2 =
        -(lambda * (threshold - theta * sigma) -
          sigma ^ 2 * lambda ^ 2 / 2) +
          (-(sigma ^ 2 / 2) * frequency ^ 2) by ring,
    Real.exp_add]
  ring

/-- The scalar Gaussian quadrature weight is bounded by its value at the left
endpoint of a nonnegative frequency interval. -/
theorem gaussianQuadratureWeight_le_at_leftEndpoint
    {alpha lambda frequencyLeft frequency : ℝ}
    (halpha : 0 ≤ alpha) (hlambda : 0 < lambda)
    (hfrequencyLeft : 0 ≤ frequencyLeft)
    (hfrequency : frequencyLeft ≤ frequency) :
    Real.exp (-alpha * frequency ^ 2) *
        (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)) ≤
      Real.exp (-alpha * frequencyLeft ^ 2) *
        (1 / Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2)) := by
  have hfrequencyNonneg : 0 ≤ frequency := hfrequencyLeft.trans hfrequency
  have hsquare : frequencyLeft ^ 2 ≤ frequency ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfrequency)
      (add_nonneg hfrequencyNonneg hfrequencyLeft)]
  have hexponential : Real.exp (-alpha * frequency ^ 2) ≤
      Real.exp (-alpha * frequencyLeft ^ 2) := by
    apply Real.exp_le_exp.mpr
    calc
      -alpha * frequency ^ 2 = -(alpha * frequency ^ 2) := by ring
      _ ≤ -(alpha * frequencyLeft ^ 2) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hsquare halpha)
      _ = -alpha * frequencyLeft ^ 2 := by ring
  have hsqrt : Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2) ≤
      Real.sqrt (lambda ^ 2 + frequency ^ 2) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrtLeft : 0 < Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2) := by
    positivity
  have hinverse : 1 / Real.sqrt (lambda ^ 2 + frequency ^ 2) ≤
      1 / Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2) :=
    one_div_le_one_div_of_le hsqrtLeft hsqrt
  exact mul_le_mul hexponential hinverse (by positivity) (Real.exp_nonneg _)

/-- The positive-frequency Gaussian quadrature tail is bounded by the Mills
factor obtained after discarding the reciprocal square root at the cutoff. -/
theorem integral_Ioi_gaussianQuadratureWeight_le_mills
    {alpha lambda cutoff C : ℝ}
    (halpha : 0 < alpha) (hlambda : 0 < lambda)
    (hcutoff : 0 < cutoff) (hconstant : 0 ≤ C) :
    (∫ frequency : ℝ in Set.Ioi cutoff,
        C * Real.exp (-alpha * frequency ^ 2) *
          (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2))) ≤
      C * Real.exp (-alpha * cutoff ^ 2) /
        (2 * alpha * cutoff ^ 2) := by
  let f : ℝ → ℝ := fun frequency =>
    C * Real.exp (-alpha * frequency ^ 2) *
      (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2))
  let g : ℝ → ℝ := fun frequency =>
    (C / cutoff) * Real.exp (-alpha * frequency ^ 2)
  have hpointwise : ∀ frequency ∈ Set.Ioi cutoff, f frequency ≤ g frequency := by
    intro frequency hfrequency
    have hfrequencyPos : 0 < frequency := hcutoff.trans hfrequency
    have hsqrtFrequency : frequency ≤
        Real.sqrt (lambda ^ 2 + frequency ^ 2) := by
      exact (Real.le_sqrt hfrequencyPos.le (by positivity)).2
        (by nlinarith [sq_nonneg lambda])
    have hinverse : 1 / Real.sqrt (lambda ^ 2 + frequency ^ 2) ≤
        1 / cutoff := by
      exact one_div_le_one_div_of_le hcutoff
        (hfrequency.le.trans hsqrtFrequency)
    dsimp only [f, g]
    calc
      C * Real.exp (-alpha * frequency ^ 2) *
          (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)) ≤
        C * Real.exp (-alpha * frequency ^ 2) * (1 / cutoff) := by
          gcongr
      _ = (C / cutoff) * Real.exp (-alpha * frequency ^ 2) := by ring
  have hgGlobal : Integrable g := by
    exact (integrable_exp_neg_mul_sq halpha).const_mul (C / cutoff)
  have hfMeasurable : AEStronglyMeasurable f := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    fun_prop
  have hf : IntegrableOn f (Set.Ioi cutoff) := by
    apply (hgGlobal.integrableOn).mono' hfMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with frequency hfrequency
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpointwise frequency hfrequency
    · dsimp only [f]
      positivity
  have hg : IntegrableOn g (Set.Ioi cutoff) := hgGlobal.integrableOn
  calc
    (∫ frequency : ℝ in Set.Ioi cutoff,
        C * Real.exp (-alpha * frequency ^ 2) *
          (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2))) =
        ∫ frequency : ℝ in Set.Ioi cutoff, f frequency := rfl
    _ ≤ ∫ frequency : ℝ in Set.Ioi cutoff, g frequency :=
      setIntegral_mono_on hf hg measurableSet_Ioi hpointwise
    _ = (C / cutoff) *
        ∫ frequency : ℝ in Set.Ioi cutoff,
          Real.exp (-alpha * frequency ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ (C / cutoff) *
        (Real.exp (-alpha * cutoff ^ 2) / (2 * alpha * cutoff)) := by
      gcongr
      exact Probability.integral_Ioi_exp_neg_mul_sq_le halpha hcutoff
    _ = C * Real.exp (-alpha * cutoff ^ 2) /
        (2 * alpha * cutoff ^ 2) := by
      field_simp

/-- Integrating a pointwise upper bound over a real `Ioc` interval multiplies
that bound by the interval length. -/
theorem integral_Ioc_le_length_mul_upperBound
    {f : ℝ → ℝ} {left right upper : ℝ}
    (hleftRight : left ≤ right)
    (hf : IntegrableOn f (Set.Ioc left right))
    (hupper : ∀ x ∈ Set.Ioc left right, f x ≤ upper) :
    (∫ x : ℝ in Set.Ioc left right, f x) ≤ (right - left) * upper := by
  calc
    (∫ x : ℝ in Set.Ioc left right, f x) ≤
        ∫ _x : ℝ in Set.Ioc left right, upper := by
      exact setIntegral_mono_on hf
        (integrableOn_const (measure_Ioc_lt_top.ne)) measurableSet_Ioc hupper
    _ = (right - left) * upper := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hleftRight)]

/-- An even power of a reciprocal square root is the corresponding power of
the reciprocal. -/
theorem one_div_sqrt_pow_two_mul (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1 / Real.sqrt x) ^ (2 * n) = (1 / x) ^ n := by
  rw [pow_mul, div_pow, one_pow, Real.sq_sqrt hx]

/-- An integrable even function on the line is twice its positive half-line
integral. -/
theorem integral_eq_two_mul_integral_Ioi_of_even
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f) :
    (∫ u : ℝ, f u) = 2 * ∫ u in Set.Ioi (0 : ℝ), f u := by
  have hneg : (∫ u in Set.Iic (0 : ℝ), f u) =
      ∫ u in Set.Ioi (0 : ℝ), f u := by
    calc
      (∫ u in Set.Iic (0 : ℝ), f u) =
          ∫ u in Set.Iic (0 : ℝ), f (-u) := by
        apply integral_congr_ae
        filter_upwards [] with u
        exact (heven u).symm
      _ = ∫ u in Set.Ioi (0 : ℝ), f u := by
        convert integral_comp_neg_Iic (0 : ℝ) f using 1
        norm_num
  rw [← intervalIntegral.integral_Iic_add_Ioi
    hf.integrableOn hf.integrableOn, hneg]
  ring

/-- The norm integrand for a finite iid row contour is absolutely
integrable. -/
theorem integrable_finiteIidQuadraticContourNorm
    {Row : Type*} [MeasurableSpace Row]
    [MeasurableSingletonClass Row]
    (rowPMF : PMF Row) (rowValue : Row → ℝ) (m : ℕ)
    (hrowIntegrable : ∀ f : Row → ℝ, Integrable f rowPMF.toMeasure)
    {sigma theta threshold lambda : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Integrable (fun u : ℝ =>
      ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
        ‖quadraticComplexMGF rowValue rowPMF.toMeasure
          (lambda + u * Complex.I) ^ m‖) := by
  let C : ℝ := mgf (fun row => rowValue row ^ 2) rowPMF.toMeasure lambda ^ m
  let X : Row → ℝ := fun row => rowValue row ^ 2
  have hExp : integrableExpSet X rowPMF.toMeasure = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact hrowIntegrable _
  have hMGF : Continuous fun u : ℝ =>
      ‖quadraticComplexMGF rowValue rowPMF.toMeasure
        (lambda + u * Complex.I) ^ m‖ := by
    have hcomplex : Continuous (complexMGF X rowPMF.toMeasure) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (analyticAt_complexMGF (by rw [hExp]; simp)).continuousAt
    exact (((hcomplex.comp (by fun_prop)).pow m).norm)
  have hweight :=
    (integrable_shiftedGaussianContourWeight
      (theta := theta) (t := threshold) hlambda hsigma).norm
  refine (hweight.const_mul C).mono'
    (hweight.aestronglyMeasurable.mul hMGF.aestronglyMeasurable) ?_
  filter_upwards [] with u
  calc
    ‖‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
        ‖quadraticComplexMGF rowValue rowPMF.toMeasure
          (lambda + u * Complex.I) ^ m‖‖ =
      ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
        ‖quadraticComplexMGF rowValue rowPMF.toMeasure
          (lambda + u * Complex.I) ^ m‖ := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ * C := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa [C] using norm_quadraticComplexMGF_pow_le rowValue
        rowPMF.toMeasure (lambda + u * Complex.I) m
    _ = C * ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ :=
      mul_comm _ _

/-- The finite iid contour norm is twice its positive-frequency half. -/
theorem integral_finiteIidQuadraticContourNorm_eq_two_mul_Ioi
    {Row : Type*} [MeasurableSpace Row]
    [MeasurableSingletonClass Row]
    (rowPMF : PMF Row) (rowValue : Row → ℝ) (m : ℕ)
    (hrowIntegrable : ∀ f : Row → ℝ, Integrable f rowPMF.toMeasure)
    {sigma theta threshold lambda : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    (∫ u : ℝ,
      ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
        ‖quadraticComplexMGF rowValue rowPMF.toMeasure
          (lambda + u * Complex.I) ^ m‖) =
      2 * ∫ u in Set.Ioi (0 : ℝ),
        ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
          ‖quadraticComplexMGF rowValue rowPMF.toMeasure
            (lambda + u * Complex.I) ^ m‖ := by
  apply integral_eq_two_mul_integral_Ioi_of_even
    (integrable_finiteIidQuadraticContourNorm rowPMF rowValue m
      hrowIntegrable hlambda hsigma)
  intro u
  dsimp only
  rw [norm_shiftedGaussianContourWeight_neg]
  congr 1
  have harg : ((lambda : ℂ) + ((-u : ℝ) : ℂ) * Complex.I) =
      (lambda : ℂ) - (u : ℂ) * Complex.I := by
    rw [Complex.ofReal_neg]
    ring
  rw [harg]
  exact norm_quadraticComplexMGF_pow_neg_eq rowValue rowPMF.toMeasure
    lambda u m

/-- The strict upper event for a finite iid quadratic statistic is bounded by
the exact shifted-Gaussian contour. -/
theorem finiteIidRowValueSqNorm_toReal_le_contour
    {m : ℕ} {Row : Type*} [Countable Row] [MeasurableSpace Row]
    [MeasurableSingletonClass Row]
    (rowPMF : PMF Row) (matrixPMF : PMF (Fin m → Row))
    (hpi : matrixPMF.toMeasure =
      Measure.pi (fun _ : Fin m => rowPMF.toMeasure))
    (hmatrixIntegrable : ∀ f : (Fin m → Row) → ℝ,
      Integrable f matrixPMF.toMeasure)
    (rowValue : Row → ℝ) {sigma theta t lambda : ℝ}
    (hsigma : 0 < sigma) (hlambda : 0 < lambda) :
    (eventProbability matrixPMF
        (fun rows => t < iidRowValueSqNorm rowValue rows)).toReal ≤
      ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖quadraticComplexMGF rowValue rowPMF.toMeasure
          (lambda + u * Complex.I) ^ m‖ := by
  let X : (Fin m → Row) → ℝ := iidRowValueSqNorm rowValue
  have hX : Measurable X := measurable_of_countable _
  have hsmooth : Integrable
      (fun rows => shiftedGaussianSmoothing sigma theta t (X rows))
      matrixPMF.toMeasure := hmatrixIntegrable _
  have hreal : Integrable (fun rows => Real.exp (lambda * X rows))
      matrixPMF.toMeasure := hmatrixIntegrable _
  rw [eventProbability_eq_toMeasure]
  calc
    matrixPMF.toMeasure.real (X ⁻¹' Set.Ioi t) ≤
        ∫ rows, shiftedGaussianSmoothing sigma theta t (X rows)
          ∂matrixPMF.toMeasure :=
      measureReal_strictUpper_preimage_le_integral_shiftedGaussianSmoothing
        _ hX hsigma hsmooth
    _ ≤ ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖complexMGF X matrixPMF.toMeasure (lambda + u * Complex.I)‖ :=
      integral_shiftedGaussianSmoothing_le_contour X hX
        (integrable_shiftedGaussianContourWeight hlambda hsigma)
        hreal (shiftedGaussianSmoothing_contourRepresentation hlambda hsigma)
    _ = ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖quadraticComplexMGF rowValue rowPMF.toMeasure
          (lambda + u * Complex.I) ^ m‖ := by
      apply integral_congr_ae
      filter_upwards [] with u
      congr 1
      rw [hpi]
      exact congrArg norm
        (complexMGF_iidRowValueSqNorm_eq_pow rowPMF rowValue
          (lambda + u * Complex.I))

/-- Positive-frequency form of the finite iid contour bound. -/
theorem finiteIidRowValueSqNorm_toReal_le_positiveContour
    {m : ℕ} {Row : Type*} [Countable Row] [MeasurableSpace Row]
    [MeasurableSingletonClass Row]
    (rowPMF : PMF Row) (matrixPMF : PMF (Fin m → Row))
    (hpi : matrixPMF.toMeasure =
      Measure.pi (fun _ : Fin m => rowPMF.toMeasure))
    (hrowIntegrable : ∀ f : Row → ℝ, Integrable f rowPMF.toMeasure)
    (hmatrixIntegrable : ∀ f : (Fin m → Row) → ℝ,
      Integrable f matrixPMF.toMeasure)
    (rowValue : Row → ℝ) {sigma theta t lambda : ℝ}
    (hsigma : 0 < sigma) (hlambda : 0 < lambda) :
    (eventProbability matrixPMF
        (fun rows => t < iidRowValueSqNorm rowValue rows)).toReal ≤
      2 * ∫ u in Set.Ioi (0 : ℝ),
        ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
          ‖quadraticComplexMGF rowValue rowPMF.toMeasure
            (lambda + u * Complex.I) ^ m‖ := by
  calc
    (eventProbability matrixPMF
        (fun rows => t < iidRowValueSqNorm rowValue rows)).toReal ≤
      ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖quadraticComplexMGF rowValue rowPMF.toMeasure
          (lambda + u * Complex.I) ^ m‖ :=
      finiteIidRowValueSqNorm_toReal_le_contour rowPMF matrixPMF hpi
        hmatrixIntegrable rowValue hsigma hlambda
    _ = 2 * ∫ u in Set.Ioi (0 : ℝ),
        ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
          ‖quadraticComplexMGF rowValue rowPMF.toMeasure
            (lambda + u * Complex.I) ^ m‖ :=
      integral_finiteIidQuadraticContourNorm_eq_two_mul_Ioi
        rowPMF rowValue m hrowIntegrable hlambda hsigma

end CertifiedJL
