/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.FourierQuantitative
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Lower
import CertifiedJL.Statements.Transport.LInfToL2
import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.LInf.Lower.Affine

/-!
# Affine sparse threshold lower tails

This file isolates the shift-stable proof spine.  A fixed additive shift is
allowed in every row.  Pointwise domination by the wrapped Gaussian followed
by positive-Fourier phase deletion reduces the affine row transform to the
same unshifted wrapped-row obligation used by the existing providers.
-/

open MeasureTheory

namespace CertifiedJL

/-- Analytic affine lower-failure event at a real dimensionless squared norm
threshold.  Public statements use the exact rational event below; this form
is the convenient boundary for a parameter-uniform Laplace argument. -/
def AffineL2RealThresholdLowerFailure (squaredNormFloor : ℝ)
    (inputThreshold q : ℕ) {rows d : ℕ} (shift : Fin rows → ℤ)
    (w : Fin d → ℤ) (J : Fin rows → Fin d → ℤ) : Prop :=
  (shiftedModularProjectionSqNorm q shift J w : ℝ) <
    squaredNormFloor * (inputThreshold : ℝ) ^ 2

private theorem affineThresholdLower_integrable_sparseRow
    {d : ℕ} (f : (Fin d → ℤ) → ℝ) :
    Integrable f (sparseRademacherRow d).toMeasure := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (SparseRowSeed d))
    (f := sparseRow) (measurable_of_finite sparseRow)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite sparseRow).aemeasurable).2
  exact Integrable.of_finite

/-- Dimensionless affine tensorization at an arbitrary real squared norm threshold.
The shifts may differ by row, but are fixed before the matrix is sampled. -/
theorem ternaryAffineThresholdLowerTail_from_rowKernelIntegral_real_at
    (rows q d : ℕ) (squaredNormFloor : ℝ) (shift : Fin rows → ℤ)
    (w : Fin d → ℤ) (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∀ j, ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          affineSparseLowerRowKernel q (shift j) w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K) :
    (eventProbability (sparseRademacherMatrix rows d)
        (AffineL2RealThresholdLowerFailure squaredNormFloor inputThreshold q shift w)).toReal ≤
      Real.exp (squaredNormFloor * s) * K ^ rows := by
  let f : Fin rows → (Fin d → ℤ) → ℝ :=
    fun j row => affineSparseLowerRowKernel q (shift j) w row
  have henergy (J : Matrix (Fin rows) (Fin d) ℤ) :
      ∑ j, f j (J j) = (shiftedModularProjectionSqNorm q shift J w : ℝ) := by
    change (∑ j,
        (centeredMod q (shift j + rowDot J w j) : ℝ) ^ 2) =
      (shiftedModularProjectionSqNorm q shift J w : ℝ)
    exact (realCast_shiftedModularProjectionSqNorm shift J w).symm
  have hevent :
      (fun J : Matrix (Fin rows) (Fin d) ℤ =>
        ∑ j, f j (J j) < squaredNormFloor * (inputThreshold : ℝ) ^ 2) =
        AffineL2RealThresholdLowerFailure squaredNormFloor inputThreshold q shift w := by
    funext J
    apply propext
    rw [henergy]
    rfl
  have ht : 0 < s / (inputThreshold : ℝ) ^ 2 := by
    have hinputThresholdReal : 0 < (inputThreshold : ℝ) := by
      exact_mod_cast hinputThreshold
    positivity
  have hbase :=
    sparseRademacherMatrix_eventProbability_toReal_strictNegativeLaplace
      (m := rows) d f (s / (inputThreshold : ℝ) ^ 2)
        (squaredNormFloor * (inputThreshold : ℝ) ^ 2) ht
  have hprod :
      ∏ j, ∫ row,
          Real.exp (-(s / (inputThreshold : ℝ) ^ 2) * f j row)
            ∂(sparseRademacherRow d).toMeasure ≤ K ^ rows := by
    calc
      ∏ j, ∫ row,
            Real.exp (-(s / (inputThreshold : ℝ) ^ 2) * f j row)
              ∂(sparseRademacherRow d).toMeasure ≤
          ∏ _j : Fin rows, K := by
        apply Finset.prod_le_prod
        · intro j hj
          exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall (fun row => Real.exp_nonneg _))
        · intro j hj
          simpa [f] using hK j
      _ = K ^ rows := by simp [Finset.prod_const, Fintype.card_fin]
  have hinputThresholdReal : (inputThreshold : ℝ) ≠ 0 := by
    exact_mod_cast hinputThreshold.ne'
  calc
    (eventProbability (sparseRademacherMatrix rows d)
        (AffineL2RealThresholdLowerFailure squaredNormFloor inputThreshold q shift w)).toReal ≤
        Real.exp ((s / (inputThreshold : ℝ) ^ 2) *
          (squaredNormFloor * (inputThreshold : ℝ) ^ 2)) *
          ∏ j, ∫ row,
            Real.exp (-(s / (inputThreshold : ℝ) ^ 2) * f j row)
              ∂(sparseRademacherRow d).toMeasure := by
      rw [← hevent]
      exact hbase
    _ ≤ Real.exp ((s / (inputThreshold : ℝ) ^ 2) *
          (squaredNormFloor * (inputThreshold : ℝ) ^ 2)) * K ^ rows := by
      exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (squaredNormFloor * s) * K ^ rows := by
      congr 2
      field_simp

/-- Exact rational thresholds agree with the analytic real-threshold event.
The public event remains cross-multiplied natural arithmetic. -/
theorem affineL2RealThresholdLowerFailure_toReal_iff
    (squaredNormFloor : NonnegativeRatio) (inputThreshold q : ℕ) {rows d : ℕ}
    (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) :
    AffineL2RealThresholdLowerFailure squaredNormFloor.toReal inputThreshold q shift w J ↔
      AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q shift w J := by
  have hdenom : 0 < (squaredNormFloor.denominator : ℝ) := by
    exact_mod_cast squaredNormFloor.denominator_pos
  have hthreshold :
      squaredNormFloor.toReal * (inputThreshold : ℝ) ^ 2 =
        ((squaredNormFloor.numerator * inputThreshold ^ 2 : ℕ) : ℝ) /
          squaredNormFloor.denominator := by
    unfold NonnegativeRatio.toReal
    push_cast
    ring
  unfold AffineL2RealThresholdLowerFailure AffineL2ThresholdLowerFailure
  rw [hthreshold, lt_div_iff₀ hdenom]
  norm_cast
  simp [mul_comm]

/-- Exact-rational event adapter for the real-threshold Laplace theorem. -/
theorem ternaryAffineThresholdLowerTail_from_rowKernelIntegral_ratio_at
    (rows q d : ℕ) (squaredNormFloor : NonnegativeRatio) (shift : Fin rows → ℤ)
    (w : Fin d → ℤ) (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∀ j, ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          affineSparseLowerRowKernel q (shift j) w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K) :
    (eventProbability (sparseRademacherMatrix rows d)
        (AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q shift w)).toReal ≤
      Real.exp (squaredNormFloor.toReal * s) * K ^ rows := by
  have hevent :
      AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q shift w =
        AffineL2RealThresholdLowerFailure squaredNormFloor.toReal inputThreshold q shift w := by
    funext J
    exact propext (affineL2RealThresholdLowerFailure_toReal_iff
      squaredNormFloor inputThreshold q shift w J).symm
  rw [hevent]
  exact ternaryAffineThresholdLowerTail_from_rowKernelIntegral_real_at
    rows q d squaredNormFloor.toReal shift w inputThreshold s K hinputThreshold hs hK

/-- The affine centered-Gaussian row transform is bounded by an unshifted
wrapped-Gaussian transform of any retained coordinate subprofile.  Neither
the shift nor the deleted coordinates incur a numerical loss. -/
theorem sparseRow_affineCenteredGaussian_le_wrappedGaussianKernel_restrict
    {q d : ℕ} (shift : ℤ) (w : Fin d → ℤ)
    (support : Finset (Fin d)) {s : ℝ}
    (hq : Odd q) (hs : 0 < s) :
    ∫ row, Real.exp (-s * affineSparseLowerRowKernel q shift w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∫ row, wrappedGaussianKernel q s
          (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure := by
  calc
    ∫ row, Real.exp (-s * affineSparseLowerRowKernel q shift w row)
        ∂(sparseRademacherRow d).toMeasure ≤
        ∫ row, wrappedGaussianKernel q s
          (shift + ∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure := by
      apply integral_mono (affineThresholdLower_integrable_sparseRow _)
        (affineThresholdLower_integrable_sparseRow _)
      intro row
      simpa only [affineSparseLowerRowKernel_apply] using
        centeredGaussian_le_wrappedGaussianKernel hq hs
          (shift + ∑ i, row i * w i)
    _ ≤ ∫ row, wrappedGaussianKernel q s
          (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure :=
      sparseRow_shiftedWrappedGaussianKernel_le_unshifted_restrict
        (q := q) shift w support hq.pos hs

/-- Dimensionless affine threshold lower-tail tensorization.  The row shifts
may differ, but are fixed before the random matrix is sampled. -/
theorem ternaryAffineThresholdLowerTail_from_rowKernelIntegral_at
    (rows squaredNormFloor q d : ℕ) (shift : Fin rows → ℤ)
    (w : Fin d → ℤ) (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∀ j, ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          affineSparseLowerRowKernel q (shift j) w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K) :
    (eventProbability (sparseRademacherMatrix rows d)
        (AffineL2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q shift w)).toReal ≤
      Real.exp (squaredNormFloor * s) * K ^ rows := by
  let f : Fin rows → (Fin d → ℤ) → ℝ :=
    fun j row => affineSparseLowerRowKernel q (shift j) w row
  have henergy (J : Matrix (Fin rows) (Fin d) ℤ) :
      ∑ j, f j (J j) = (shiftedModularProjectionSqNorm q shift J w : ℝ) := by
    change (∑ j,
        (centeredMod q (shift j + rowDot J w j) : ℝ) ^ 2) =
      (shiftedModularProjectionSqNorm q shift J w : ℝ)
    exact (realCast_shiftedModularProjectionSqNorm shift J w).symm
  have hevent :
      (fun J : Matrix (Fin rows) (Fin d) ℤ =>
        ∑ j, f j (J j) < (squaredNormFloor : ℝ) * (inputThreshold : ℝ) ^ 2) =
        AffineL2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q shift w := by
    funext J
    apply propext
    rw [henergy]
    simp only [AffineL2ThresholdLowerFailure, NonnegativeRatio.ofNat, one_mul]
    norm_cast
  have ht : 0 < s / (inputThreshold : ℝ) ^ 2 := by
    have hinputThresholdReal : 0 < (inputThreshold : ℝ) := by
      exact_mod_cast hinputThreshold
    positivity
  have hbase :=
    sparseRademacherMatrix_eventProbability_toReal_strictNegativeLaplace
      (m := rows) d f (s / (inputThreshold : ℝ) ^ 2)
        ((squaredNormFloor : ℝ) * (inputThreshold : ℝ) ^ 2) ht
  have hbase' :
      (eventProbability (sparseRademacherMatrix rows d)
          (AffineL2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
            inputThreshold q shift w)).toReal ≤
        Real.exp ((s / (inputThreshold : ℝ) ^ 2) *
          ((squaredNormFloor : ℝ) * (inputThreshold : ℝ) ^ 2)) *
          ∏ j, ∫ row,
            Real.exp (-(s / (inputThreshold : ℝ) ^ 2) * f j row)
              ∂(sparseRademacherRow d).toMeasure := by
    rw [← hevent]
    exact hbase
  have hprod :
      ∏ j, ∫ row,
          Real.exp (-(s / (inputThreshold : ℝ) ^ 2) * f j row)
            ∂(sparseRademacherRow d).toMeasure ≤ K ^ rows := by
    calc
      ∏ j, ∫ row,
            Real.exp (-(s / (inputThreshold : ℝ) ^ 2) * f j row)
              ∂(sparseRademacherRow d).toMeasure ≤
          ∏ _j : Fin rows, K := by
        apply Finset.prod_le_prod
        · intro j hj
          exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall (fun row => Real.exp_nonneg _))
        · intro j hj
          simpa [f] using hK j
      _ = K ^ rows := by simp [Finset.prod_const, Fintype.card_fin]
  have hinputThresholdReal : (inputThreshold : ℝ) ≠ 0 := by
    exact_mod_cast hinputThreshold.ne'
  calc
    (eventProbability (sparseRademacherMatrix rows d)
        (AffineL2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q shift w)).toReal ≤
        Real.exp ((s / (inputThreshold : ℝ) ^ 2) *
          ((squaredNormFloor : ℝ) * (inputThreshold : ℝ) ^ 2)) *
          ∏ j, ∫ row,
            Real.exp (-(s / (inputThreshold : ℝ) ^ 2) * f j row)
              ∂(sparseRademacherRow d).toMeasure := hbase'
    _ ≤ Real.exp ((s / (inputThreshold : ℝ) ^ 2) *
          ((squaredNormFloor : ℝ) * (inputThreshold : ℝ) ^ 2)) * K ^ rows := by
      exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (squaredNormFloor * s) * K ^ rows := by
      congr 2
      field_simp

/-- Complete affine event bound from one unshifted wrapped-row bound.  This is
the formal boundary consumed by phase-stable numerical certificates. -/
theorem ternaryAffineThresholdLowerTail_lt_failureTarget_of_wrappedRow_at
    (rows squaredNormFloor bits q d : ℕ) (shift : Fin rows → ℤ)
    (w : Fin d → ℤ) (support : Finset (Fin d))
    (inputThreshold : ℕ) (s K : ℝ)
    (hq : Odd q) (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hwrapped : ∫ row, wrappedGaussianKernel q
        (s / (inputThreshold : ℝ) ^ 2)
          (∑ i, row i * (if i ∈ support then w i else 0))
          ∂(sparseRademacherRow d).toMeasure ≤ K)
    (hratio : Real.exp (squaredNormFloor * s) * K ^ rows <
      (2 : ℝ)⁻¹ ^ bits) :
    eventProbability (sparseRademacherMatrix rows d)
        (AffineL2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q shift w) < failureTarget bits := by
  have hinputThresholdReal : 0 < (inputThreshold : ℝ) := by
    exact_mod_cast hinputThreshold
  have hscaledTilt : 0 < s / (inputThreshold : ℝ) ^ 2 := by positivity
  have hrow (j : Fin rows) :
      ∫ row, Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          affineSparseLowerRowKernel q (shift j) w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K :=
    (sparseRow_affineCenteredGaussian_le_wrappedGaussianKernel_restrict
      (shift j) w support hq hscaledTilt).trans hwrapped
  have htail := ternaryAffineThresholdLowerTail_from_rowKernelIntegral_at
    rows squaredNormFloor q d shift w inputThreshold s K hinputThreshold hs hrow
  have hreal :
      (eventProbability (sparseRademacherMatrix rows d)
        (AffineL2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q shift w)).toReal < (2 : ℝ)⁻¹ ^ bits :=
    htail.trans_lt hratio
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by simp [failureTarget])]
  simpa [failureTarget] using hreal

/-- The one-row obligation left by the affine `(rows, floor, bits) =
`(256, 29, 128)` canary.  The support and tilt may depend on the fixed public
input, but not on the sampled matrix or on the row-wise affine shift.

This is deliberately a mathematical proof boundary rather than a numerical
certificate contract. Its singleton specialization is impossible, so this
historical premise must not be used as a replay or fast-assumption target.
The underlying floor-29 probability statement is not refuted by this obstruction. -/
def AffineL2ThresholdLower256Floor29Bits128WrappedObligation : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q →
    CenteredInput q w →
    0 < inputThreshold →
    InputThresholdAtMostNorm inputThreshold w →
    InputThresholdWithinModulus (NonnegativeRatio.ofNat 3) q inputThreshold →
    ∃ (support : Finset (Fin d)) (s K : ℝ),
      0 < s ∧
      (∫ row, wrappedGaussianKernel q
          (s / (inputThreshold : ℝ) ^ 2)
            (∑ i, row i * (if i ∈ support then w i else 0))
          ∂(sparseRademacherRow d).toMeasure) ≤ K ∧
      Real.exp (29 * s) * K ^ 256 < (2 : ℝ)⁻¹ ^ 128

/-- Historical conditional reduction: the wrapped-row premise is impossible
(see `docs/affine-threshold-lower-plan.md`), so it is not a certificate target.
The exact floor-29 probability statement remains open. Assuming the premise proves the affine
balanced-ternary lower tail at exactly 256 rows, squared-norm floor 29, modulus
margin 3, and 128 bits.  All transport from that one-row boundary to the
protocol-facing theorem is kernel checked and incurs no numerical loss. -/
theorem ternaryAffineL2ThresholdLower256Floor29Bits128_of_wrappedObligation
    (hobligation :
      AffineL2ThresholdLower256Floor29Bits128WrappedObligation) :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  obtain ⟨support, s, K, hs, hwrapped, hratio⟩ :=
    hobligation q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  exact ternaryAffineThresholdLowerTail_lt_failureTarget_of_wrappedRow_at
    256 29 128 q d shift w support inputThreshold s K hq hpositive hs
      hwrapped hratio

/-- The same wrapped-row obligation gives the exact coordinate cap `67/200`
at 256 rows and 128 bits.  This is a deterministic consequence of the affine
floor-29 squared-norm statement. -/
theorem ternaryAffineLInfThresholdLower256Cap67Over200Bits128_of_wrappedObligation
    (hobligation :
      AffineL2ThresholdLower256Floor29Bits128WrappedObligation) :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 67, denominator := 200, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) :=
  affineLInfThresholdLowerTailAt_of_affineL2
    .balancedTernary 256
      { numerator := 67, denominator := 200, denominator_pos := by decide }
      (NonnegativeRatio.ofNat 29) (NonnegativeRatio.ofNat 3)
      (failureTarget 128) rows256_cap67div200_fits_squaredNormFloor29
      (ternaryAffineL2ThresholdLower256Floor29Bits128_of_wrappedObligation
        hobligation)

end CertifiedJL
