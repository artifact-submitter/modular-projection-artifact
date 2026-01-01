/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineL2General
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.NearVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseFloor73Verified

/-! # General affine Euclidean bounds with verified wrapped-profile providers -/

namespace CertifiedJL.Results.Affine.L2.Lower.General

open CertifiedJL

private theorem profiles : CertificateAssembly.AffineL2WrappedProfiles :=
  CertificateAssembly.affineL2General_profiles
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified
    CertificateProviders.sparseL2ThresholdDiffuseFloor73Endpoints_verified

/-- General affine squared-norm bound at a chosen admissible singleton tilt. -/
theorem ternaryAffineL2LowerTail_toReal_le_finiteTilt
    (rows q d b : ℕ) (L : ℝ) (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (t : ℝ) (hq : Odd q) (hb : 0 < b) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q)
    (ht : (1250 / 2401 : ℝ) ≤ t) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineL2RealThresholdLowerFailure L b q shift w)).toReal ≤
        max (affineL2SingletonTiltBound rows L t)
          (max (affineL2NearBound rows L) (affineL2DiffuseBound rows L)) :=
  CertifiedJL.ternaryAffineL2LowerTail_toReal_le_finiteTilt
    rows q d b L shift w t hq hb hcentered hnorm hmargin ht
    profiles.near profiles.diffuse33 profiles.diffuse25

/-- General affine squared-norm bound with the infimum over singleton tilts.
The input and the row-wise shift are fixed before sampling the matrix. -/
theorem ternaryAffineL2LowerTail_toReal_le_general
    (rows q d b : ℕ) (L : ℝ) (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (hL : 0 ≤ L) (hq : Odd q) (hb : 0 < b) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineL2RealThresholdLowerFailure L b q shift w)).toReal ≤
        affineL2GeneralBound rows L :=
  CertifiedJL.ternaryAffineL2LowerTail_toReal_le_general
    rows q d b L shift w hL hq hb hcentered hnorm hmargin
    profiles.near profiles.diffuse33 profiles.diffuse25

/-- Exact rational-floor presentation with natural squared norm. -/
theorem ternaryAffineL2LowerTail_toReal_le_general_of_ratio
    (rows q d b : ℕ) (squaredNormFloor : NonnegativeRatio)
    (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (hq : Odd q) (hb : 0 < b) (hcentered : CenteredInput q w)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineL2ThresholdLowerFailure squaredNormFloor b q shift w)).toReal ≤
        affineL2GeneralBound rows squaredNormFloor.toReal :=
  CertifiedJL.ternaryAffineL2LowerTail_toReal_le_general_of_ratio
    rows q d b squaredNormFloor shift w hq hb hcentered hnorm hmargin
    profiles.near profiles.diffuse33 profiles.diffuse25

/-- A separate strict numerical comparison turns the general bound into an
exact affine lower-tail schema at the requested security target. -/
theorem ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget
    (rows bits : ℕ) (squaredNormFloor : NonnegativeRatio)
    (hbound : affineL2GeneralBound rows squaredNormFloor.toReal < (2 : ℝ)⁻¹ ^ bits) :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := rows, squaredNormFloor := squaredNormFloor,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget bits) :=
  CertifiedJL.ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget
    rows bits squaredNormFloor profiles.near profiles.diffuse33 profiles.diffuse25 hbound

/-- Endpoint criterion with one explicit singleton tilt and a strict numerical
comparison, shared by all planned shifted Euclidean endpoints. -/
theorem ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget
    (rows bits : ℕ) (squaredNormFloor : NonnegativeRatio) (t : ℝ)
    (ht : (1250 / 2401 : ℝ) ≤ t)
    (hbound :
      max (affineL2SingletonTiltBound rows squaredNormFloor.toReal t)
        (max (affineL2NearBound rows squaredNormFloor.toReal)
          (affineL2DiffuseBound rows squaredNormFloor.toReal)) < (2 : ℝ)⁻¹ ^ bits) :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := rows, squaredNormFloor := squaredNormFloor,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget bits) :=
  CertifiedJL.ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget
    rows bits squaredNormFloor t ht profiles.near profiles.diffuse33 profiles.diffuse25 hbound

end CertifiedJL.Results.Affine.L2.Lower.General
