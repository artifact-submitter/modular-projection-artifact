/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Singleton.GaussianRow
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedProfiles

/-!
# General affine sparse L2 lower tail

This module assembles the singleton, near, and diffuse retained-profile
estimates.  The branch is determined by the fixed input, so the resulting
bound is a maximum of branch estimates without a union-bound loss.
-/

open MeasureTheory Set

namespace CertifiedJL

/-- The three exhaustive fixed-input profile classes. Closed boundary choices
send `49/50` to the singleton class and `3/4` to the diffuse class. -/
theorem thresholdProfile_singleton_near_diffuse
    {d b : ℕ} (w : Fin d → ℤ) :
    (∃ i, 49 * b ≤ 50 * (w i).natAbs) ∨
      ((∀ i, 50 * (w i).natAbs ≤ 49 * b) ∧
        (∃ i, 3 * b < 4 * (w i).natAbs)) ∨
      (∀ i, 4 * (w i).natAbs ≤ 3 * b) := by
  by_cases hsingleton : ∃ i, 49 * b ≤ 50 * (w i).natAbs
  · exact Or.inl hsingleton
  · right
    have hbelow : ∀ i, 50 * (w i).natAbs ≤ 49 * b := by
      intro i
      exact (Nat.lt_of_not_ge (not_exists.mp hsingleton i)).le
    by_cases hnear : ∃ i, 3 * b < 4 * (w i).natAbs
    · exact Or.inl ⟨hbelow, hnear⟩
    · exact Or.inr (fun i => Nat.le_of_not_lt (not_exists.mp hnear i))

/-- The singleton contribution at one admissible tilt. -/
noncomputable def affineL2SingletonTiltBound (rows : ℕ) (L t : ℝ) : ℝ :=
  Real.exp (L * t) * singletonGaussianEnvelope t ^ rows

/-- The frozen near-profile contribution. -/
noncomputable def affineL2NearBound (rows : ℕ) (L : ℝ) : ℝ :=
  Real.exp (L * (23 / 10)) * (681 / 1250) ^ rows

/-- The better of the two frozen diffuse-profile contributions. -/
noncomputable def affineL2DiffuseBound (rows : ℕ) (L : ℝ) : ℝ :=
  min
    (Real.exp (L * (33 / 10)) * (97 / 200) ^ rows)
    (Real.exp (L * (5 / 2)) * (539 / 1000) ^ rows)

/-- All admissible singleton-tilt values. -/
noncomputable def affineL2SingletonTiltValues (rows : ℕ) (L : ℝ) : Set ℝ :=
  affineL2SingletonTiltBound rows L '' Ici (1250 / 2401)

/-- The singleton infimum used by the general bound. -/
noncomputable def affineL2SingletonInfimum (rows : ℕ) (L : ℝ) : ℝ :=
  sInf (affineL2SingletonTiltValues rows L)

/-- The general three-profile affine L2 bound. -/
noncomputable def affineL2GeneralBound (rows : ℕ) (L : ℝ) : ℝ :=
  max (affineL2SingletonInfimum rows L)
    (max (affineL2NearBound rows L) (affineL2DiffuseBound rows L))

/-- The admissible singleton tilt set has an explicit witness. -/
theorem affineL2SingletonTiltValues_nonempty (rows : ℕ) (L : ℝ) :
    (affineL2SingletonTiltValues rows L).Nonempty := by
  refine ⟨affineL2SingletonTiltBound rows L (1250 / 2401), ?_⟩
  exact ⟨1250 / 2401, by norm_num, rfl⟩

private theorem singletonGaussianEnvelope_pos_of_admissible
    {t : ℝ} (ht : (1250 / 2401 : ℝ) ≤ t) :
    0 < singletonGaussianEnvelope t := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hexp : Real.exp (-9 * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  unfold singletonGaussianEnvelope
  positivity

/-- Singleton tilt values are explicitly bounded below by zero. -/
theorem affineL2SingletonTiltValues_bddBelow (rows : ℕ) (L : ℝ) :
    BddBelow (affineL2SingletonTiltValues rows L) := by
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (singletonGaussianEnvelope_pos_of_admissible ht).le _)

/-- The infimum is no larger than any explicitly chosen admissible tilt. -/
theorem affineL2SingletonInfimum_le_tilt
    (rows : ℕ) (L t : ℝ) (ht : (1250 / 2401 : ℝ) ≤ t) :
    affineL2SingletonInfimum rows L ≤ affineL2SingletonTiltBound rows L t := by
  exact csInf_le (affineL2SingletonTiltValues_bddBelow rows L) ⟨t, ht, rfl⟩

/-- The infimum formula improves every finite admissible-tilt formula. -/
theorem affineL2GeneralBound_le_finiteTilt
    (rows : ℕ) (L t : ℝ) (ht : (1250 / 2401 : ℝ) ≤ t) :
    affineL2GeneralBound rows L ≤
      max (affineL2SingletonTiltBound rows L t)
        (max (affineL2NearBound rows L) (affineL2DiffuseBound rows L)) := by
  exact max_le_max (affineL2SingletonInfimum_le_tilt rows L t ht) le_rfl

/-- Finite-tilt assembly. Different singleton, near, and diffuse tilts are
used in their fixed-input branches, with no probability union bound. -/
theorem ternaryAffineL2LowerTail_toReal_le_finiteTilt
    (rows q d b : ℕ) (L : ℝ) (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (t : ℝ) (hq : Odd q) (hb : 0 < b) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q)
    (ht : (1250 / 2401 : ℝ) ≤ t)
    (hnear : SparseThresholdNearWrappedRowBound)
    (hdiffuse33 : SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200))
    (hdiffuse25 : SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000)) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineL2RealThresholdLowerFailure L b q shift w)).toReal ≤
        max (affineL2SingletonTiltBound rows L t)
          (max (affineL2NearBound rows L) (affineL2DiffuseBound rows L)) := by
  rcases thresholdProfile_singleton_near_diffuse w with
      hsingleton | ⟨hbelow, hnearCoordinate⟩ | hdiffuse
  · obtain ⟨i, hi⟩ := hsingleton
    have hrow (j : Fin rows) :
        ∫ row, Real.exp (-(t / (b : ℝ) ^ 2) *
            affineSparseLowerRowKernel q (shift j) w row)
            ∂(sparseRademacherRow d).toMeasure ≤ singletonGaussianEnvelope t :=
      sparseRow_affineCenteredGaussian_le_singletonGaussianEnvelope_of_centeredInput
        (shift j) w i hq hb hmargin hcentered hi ht
    have htail := ternaryAffineThresholdLowerTail_from_rowKernelIntegral_real_at
      rows q d L shift w b t (singletonGaussianEnvelope t) hb
        (lt_of_lt_of_le (by norm_num) ht) hrow
    exact htail.trans (le_max_left _ _)
  · obtain ⟨support, hwrapped⟩ :=
      hnear q d w b hq hb hnorm hmargin hbelow hnearCoordinate
    have htilt : 0 < (23 / 10 : ℝ) / (b : ℝ) ^ 2 := by positivity
    have hrow (j : Fin rows) :
        ∫ row, Real.exp (-((23 / 10 : ℝ) / (b : ℝ) ^ 2) *
            affineSparseLowerRowKernel q (shift j) w row)
            ∂(sparseRademacherRow d).toMeasure ≤ 681 / 1250 :=
      (sparseRow_affineCenteredGaussian_le_wrappedGaussianKernel_restrict
        (shift j) w support hq htilt).trans hwrapped
    have htail := ternaryAffineThresholdLowerTail_from_rowKernelIntegral_real_at
      rows q d L shift w b (23 / 10) (681 / 1250) hb (by norm_num) hrow
    exact htail.trans (le_trans (le_max_left _ _ ) (le_max_right _ _))
  · obtain ⟨support33, hwrapped33⟩ :=
      hdiffuse33 q d w b hq hb hnorm hmargin hdiffuse
    obtain ⟨support25, hwrapped25⟩ :=
      hdiffuse25 q d w b hq hb hnorm hmargin hdiffuse
    have hrow33 (j : Fin rows) :
        ∫ row, Real.exp (-((33 / 10 : ℝ) / (b : ℝ) ^ 2) *
            affineSparseLowerRowKernel q (shift j) w row)
            ∂(sparseRademacherRow d).toMeasure ≤ 97 / 200 :=
      (sparseRow_affineCenteredGaussian_le_wrappedGaussianKernel_restrict
        (shift j) w support33 hq (by positivity)).trans hwrapped33
    have hrow25 (j : Fin rows) :
        ∫ row, Real.exp (-((5 / 2 : ℝ) / (b : ℝ) ^ 2) *
            affineSparseLowerRowKernel q (shift j) w row)
            ∂(sparseRademacherRow d).toMeasure ≤ 539 / 1000 :=
      (sparseRow_affineCenteredGaussian_le_wrappedGaussianKernel_restrict
        (shift j) w support25 hq (by positivity)).trans hwrapped25
    have htail33 := ternaryAffineThresholdLowerTail_from_rowKernelIntegral_real_at
      rows q d L shift w b (33 / 10) (97 / 200) hb (by norm_num) hrow33
    have htail25 := ternaryAffineThresholdLowerTail_from_rowKernelIntegral_real_at
      rows q d L shift w b (5 / 2) (539 / 1000) hb (by norm_num) hrow25
    have htail :
        (eventProbability (sparseRademacherMatrix rows d)
          (AffineL2RealThresholdLowerFailure L b q shift w)).toReal ≤
            affineL2DiffuseBound rows L := by
      exact le_min htail33 htail25
    exact htail.trans (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Infimum form of the general affine L2 theorem. No minimizing tilt or
optimizer existence is required. -/
theorem ternaryAffineL2LowerTail_toReal_le_general
    (rows q d b : ℕ) (L : ℝ) (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (_hL : 0 ≤ L) (hq : Odd q) (hb : 0 < b) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q)
    (hnear : SparseThresholdNearWrappedRowBound)
    (hdiffuse33 : SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200))
    (hdiffuse25 : SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000)) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineL2RealThresholdLowerFailure L b q shift w)).toReal ≤
        affineL2GeneralBound rows L := by
  let P := (eventProbability (sparseRademacherMatrix rows d)
    (AffineL2RealThresholdLowerFailure L b q shift w)).toReal
  let C := max (affineL2NearBound rows L) (affineL2DiffuseBound rows L)
  by_cases hPC : P ≤ C
  · exact hPC.trans (le_max_right _ _)
  · have hPinf : P ≤ affineL2SingletonInfimum rows L := by
      apply le_csInf (affineL2SingletonTiltValues_nonempty rows L)
      intro x hx
      obtain ⟨t, ht, rfl⟩ := hx
      have hfinite := ternaryAffineL2LowerTail_toReal_le_finiteTilt
        rows q d b L shift w t hq hb hcentered hnorm hmargin ht
          hnear hdiffuse33 hdiffuse25
      change P ≤ max (affineL2SingletonTiltBound rows L t) C at hfinite
      by_contra hnot
      have hleft : affineL2SingletonTiltBound rows L t < P := lt_of_not_ge hnot
      have hright : C < P := lt_of_not_ge hPC
      exact (not_lt_of_ge hfinite) (max_lt hleft hright)
    exact hPinf.trans (le_max_left _ _)

/-- Exact-rational, natural squared-norm presentation of the general
analytic bound. -/
theorem ternaryAffineL2LowerTail_toReal_le_general_of_ratio
    (rows q d b : ℕ) (squaredNormFloor : NonnegativeRatio)
    (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (hq : Odd q) (hb : 0 < b) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q)
    (hnear : SparseThresholdNearWrappedRowBound)
    (hdiffuse33 : SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200))
    (hdiffuse25 : SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000)) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineL2ThresholdLowerFailure squaredNormFloor b q shift w)).toReal ≤
        affineL2GeneralBound rows squaredNormFloor.toReal := by
  have hL : 0 ≤ squaredNormFloor.toReal := by
    unfold NonnegativeRatio.toReal
    positivity
  have hevent :
      AffineL2ThresholdLowerFailure squaredNormFloor b q shift w =
        AffineL2RealThresholdLowerFailure squaredNormFloor.toReal b q shift w := by
    funext J
    exact propext (affineL2RealThresholdLowerFailure_toReal_iff
      squaredNormFloor b q shift w J).symm
  rw [hevent]
  exact ternaryAffineL2LowerTail_toReal_le_general rows q d b
    squaredNormFloor.toReal shift w hL hq hb hcentered hnorm hmargin
      hnear hdiffuse33 hdiffuse25

/-- A strict numerical bound on the one general formula supplies an exact
public affine threshold theorem at modulus margin three. -/
theorem ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget
    (rows bits : ℕ) (squaredNormFloor : NonnegativeRatio)
    (hnear : SparseThresholdNearWrappedRowBound)
    (hdiffuse33 : SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200))
    (hdiffuse25 : SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000))
    (hbound : affineL2GeneralBound rows squaredNormFloor.toReal < (2 : ℝ)⁻¹ ^ bits) :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := rows
        squaredNormFloor := squaredNormFloor
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget bits) := by
  intro q d w b shift hq hcentered hb hnorm hmodulus
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  have hmargin : 3 * b ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmodulus
  have htail := ternaryAffineL2LowerTail_toReal_le_general_of_ratio
    rows q d b squaredNormFloor shift w hq hb hcentered hnorm hmargin
      hnear hdiffuse33 hdiffuse25
  have hreal :
      (eventProbability (sparseRademacherMatrix rows d)
        (AffineL2ThresholdLowerFailure squaredNormFloor b q shift w)).toReal <
          (2 : ℝ)⁻¹ ^ bits := htail.trans_lt hbound
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by simp [failureTarget])]
  simpa [failureTarget] using hreal

/-- Endpoint-friendly exact schema adapter using one explicit admissible
singleton tilt. -/
theorem ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget
    (rows bits : ℕ) (squaredNormFloor : NonnegativeRatio) (t : ℝ)
    (ht : (1250 / 2401 : ℝ) ≤ t)
    (hnear : SparseThresholdNearWrappedRowBound)
    (hdiffuse33 : SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200))
    (hdiffuse25 : SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000))
    (hbound :
      max (affineL2SingletonTiltBound rows squaredNormFloor.toReal t)
        (max (affineL2NearBound rows squaredNormFloor.toReal)
          (affineL2DiffuseBound rows squaredNormFloor.toReal)) < (2 : ℝ)⁻¹ ^ bits) :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := rows
        squaredNormFloor := squaredNormFloor
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget bits) := by
  apply ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget
    rows bits squaredNormFloor hnear hdiffuse33 hdiffuse25
  exact (affineL2GeneralBound_le_finiteTilt
    rows squaredNormFloor.toReal t ht).trans_lt hbound

end CertifiedJL
