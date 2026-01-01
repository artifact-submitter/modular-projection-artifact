/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.LowerRowKernel
import CertifiedJL.Analysis.SmoothBounds.NegativeLaplace
import CertifiedJL.Statements.L2.Lower

/-!
# Sparse protocol-threshold lower-tail assembly

This module isolates the one genuinely analytic obligation for a
protocol-facing sparse lower tail.  Unlike the older cap-relative proof, the
row kernel is normalized by a public threshold that may be strictly smaller
than the actual input norm.
-/

open MeasureTheory

namespace CertifiedJL

/-- Dimensionless protocol-threshold form of the balanced-ternary lower-tail
trunk. The row transform is normalized by the public `inputThreshold`, not by
the actual norm of `w`. -/
theorem ternaryThresholdLowerTail_from_rowKernelIntegral_at
    (rows squaredNormFloor q d : ℕ) (w : Fin d → ℤ)
    (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K) :
    (eventProbability (sparseRademacherMatrix rows d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w)).toReal ≤
      Real.exp (squaredNormFloor * s) * K ^ rows := by
  let f : Fin rows → (Fin d → ℤ) → ℝ :=
    fun _ row => sparseLowerRowKernel q w row
  have henergy (J : Matrix (Fin rows) (Fin d) ℤ) :
      ∑ j, f j (J j) = (modularProjectionSqNorm q J w : ℝ) := by
    change (∑ j, (centeredMod q (rowDot J w j) : ℝ) ^ 2) =
      (modularProjectionSqNorm q J w : ℝ)
    exact (realCast_modularProjectionSqNorm J w).symm
  have hevent :
      (fun J : Matrix (Fin rows) (Fin d) ℤ =>
        ∑ j, f j (J j) < (squaredNormFloor : ℝ) * (inputThreshold : ℝ) ^ 2) =
        L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w := by
    funext J
    apply propext
    rw [henergy]
    simp only [L2ThresholdLowerFailure, NonnegativeRatio.ofNat, one_mul]
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
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
            inputThreshold q w)).toReal ≤
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
          simpa [f] using hK
      _ = K ^ rows := by
        simp [Finset.prod_const, Fintype.card_fin]
  have hinputThresholdReal : (inputThreshold : ℝ) ≠ 0 := by
    exact_mod_cast hinputThreshold.ne'
  calc
    (eventProbability (sparseRademacherMatrix rows d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w)).toReal ≤
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

/-- The generic row-kernel integral bound specialized to the original
256-row, squared-norm-floor-29 endpoint. -/
theorem ternaryThresholdLowerTail_from_rowKernelIntegral
    (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K) :
    (eventProbability (sparseRademacherMatrix 256 d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
          inputThreshold q w)).toReal ≤
      Real.exp (29 * s) * K ^ 256 :=
  ternaryThresholdLowerTail_from_rowKernelIntegral_at
    256 29 q d w inputThreshold s K hinputThreshold hs hK

/-- A strict real row-kernel comparison closes a protocol-threshold event at
arbitrary row count, squared-norm floor, and bit target. -/
theorem ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_at
    (rows squaredNormFloor bits q d : ℕ) (w : Fin d → ℤ)
    (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K)
    (hratio : Real.exp (squaredNormFloor * s) * K ^ rows <
      (2 : ℝ)⁻¹ ^ bits) :
    eventProbability (sparseRademacherMatrix rows d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w) < failureTarget bits := by
  have htail := ternaryThresholdLowerTail_from_rowKernelIntegral_at
    rows squaredNormFloor q d w inputThreshold s K hinputThreshold hs hK
  have hreal :
      (eventProbability (sparseRademacherMatrix rows d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w)).toReal < (2 : ℝ)⁻¹ ^ bits :=
    htail.trans_lt hratio
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by simp [failureTarget])]
  simpa [failureTarget] using hreal

/-- Compatibility specialization at 256 rows and squared-norm floor 29. -/
theorem ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_bits
    (bits q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K)
    (hratio : Real.exp (29 * s) * K ^ 256 < (2 : ℝ)⁻¹ ^ bits) :
    eventProbability (sparseRademacherMatrix 256 d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
          inputThreshold q w) < failureTarget bits :=
  ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_at
    256 29 bits q d w inputThreshold s K hinputThreshold hs hK hratio

/-- The row-kernel endgame specialized to 128 bits. -/
theorem ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel
    (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ) (s K : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hs : 0 < s)
    (hK : ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K)
    (hratio : Real.exp (29 * s) * K ^ 256 < (2 : ℝ)⁻¹ ^ 128) :
    eventProbability (sparseRademacherMatrix 256 d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
          inputThreshold q w) < failureTarget 128 :=
  ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_bits
    128 q d w inputThreshold s K hinputThreshold hs hK hratio

/-- Uniform one-row contract for a sparse protocol-threshold theorem.

The contract retains every protocol premise so a future proof may exploit
centered representatives, excess input squared norm, and the modulus margin.  Its
conclusion is the exact row transform consumed by the tensorization theorem;
there is no certificate representation in this boundary.
-/
def SparseThresholdLowerRowBoundAt
    (modulusMargin : NonnegativeRatio) (s K : ℝ) : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q →
    CenteredInput q w →
    0 < inputThreshold →
    InputThresholdAtMostNorm inputThreshold w →
    InputThresholdWithinModulus modulusMargin q inputThreshold →
    ∫ row,
        Real.exp (-(s / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K

/-- A uniform row bound plus one strict scalar comparison proves the complete
threshold-relative statement at arbitrary rows, squared-norm floor, and bit target. -/
theorem sparseThresholdLowerTailAt_of_rowKernelBound_at
    (rows squaredNormFloor bits : ℕ) (modulusMargin : NonnegativeRatio)
    (s K : ℝ) (hs : 0 < s)
    (hrow : SparseThresholdLowerRowBoundAt modulusMargin s K)
    (hratio : Real.exp (squaredNormFloor * s) * K ^ rows <
      (2 : ℝ)⁻¹ ^ bits) :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := rows
        squaredNormFloor := NonnegativeRatio.ofNat squaredNormFloor
        modulusMargin := modulusMargin }
      (failureTarget bits) := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  exact ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_at
    rows squaredNormFloor bits q d w inputThreshold s K hpositive hs
      (hrow q d w inputThreshold hq hcentered hpositive hnorm hmodulus)
      hratio

/-- A uniform row bound plus one strict scalar comparison proves the complete
256-row, threshold-29 protocol statement at an arbitrary bit target. -/
theorem sparseThresholdLowerTailAt_of_rowKernelBound_bits
    (bits : ℕ) (modulusMargin : NonnegativeRatio) (s K : ℝ) (hs : 0 < s)
    (hrow : SparseThresholdLowerRowBoundAt modulusMargin s K)
    (hratio : Real.exp (29 * s) * K ^ 256 < (2 : ℝ)⁻¹ ^ bits) :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := modulusMargin }
      (failureTarget bits) := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  exact ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_bits
    bits q d w inputThreshold s K hpositive hs
      (hrow q d w inputThreshold hq hcentered hpositive hnorm hmodulus)
      hratio

/-- Compatibility specialization of the uniform row-bound assembly at
128 bits. -/
theorem sparseThresholdLowerTailAt_of_rowKernelBound
    (modulusMargin : NonnegativeRatio) (s K : ℝ) (hs : 0 < s)
    (hrow : SparseThresholdLowerRowBoundAt modulusMargin s K)
    (hratio : Real.exp (29 * s) * K ^ 256 < (2 : ℝ)⁻¹ ^ 128) :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := modulusMargin }
      (failureTarget 128) :=
  sparseThresholdLowerTailAt_of_rowKernelBound_bits
    128 modulusMargin s K hs hrow hratio

end CertifiedJL
