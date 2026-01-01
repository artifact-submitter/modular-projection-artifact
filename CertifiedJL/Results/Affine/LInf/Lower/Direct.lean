/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineLInf
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseFloor73Verified
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Floor73

/-! # Direct affine infinity-norm lower tails at modulus margin three -/

namespace CertifiedJL.Results.Affine.LInf.Lower.Direct

open CertifiedJL

/-- Arbitrary row-wise shifts fixed before sampling the balanced-ternary matrix. -/
theorem ternaryAffineLInfThresholdLower256Cap67Over200Bits130 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 67, denominator := 200, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 130) :=
  CertificateAssembly.affineLInfCap67Over200
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified

/-- Arbitrary row-wise shifts fixed before sampling the balanced-ternary matrix. -/
theorem ternaryAffineLInfThresholdLower256Cap6Over25Bits197 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 6, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 197) :=
  CertificateAssembly.affineLInfCap6Over25
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified

/-- The concrete shift-uniform small-ball envelope for every rational cap at most `3/8`.
Both wrapped profile providers are supplied by their verified numerical proofs. -/
theorem ternaryAffineLInfThresholdLower_probability_le
    (rows : ℕ) (cap : NonnegativeRatio)
    (hcap : 8 * cap.numerator ≤ 3 * cap.denominator)
    (q d : ℕ) (w : Fin d → ℤ) (b : ℕ) (shift : Fin rows → ℤ)
    (hq : Odd q) (hcentered : CenteredInput q w) (hb : 0 < b)
    (hnorm : InputThresholdAtMostNorm b w) (hmargin : 3 * b ≤ q) :
    (eventProbability (sparseRademacherMatrix rows d)
      (AffineLInfThresholdSmallProjection
        { distribution := .balancedTernary, rows := rows, coordinateCap := cap,
          modulusMargin := NonnegativeRatio.ofNat 3 } b q shift w)).toReal ≤
      (max (1 / 2 : ℝ) (min
        (Real.exp ((33 / 10 : ℝ) * ((cap.numerator : ℝ) / cap.denominator) ^ 2) *
          (97 / 200))
        (Real.exp ((5 / 2 : ℝ) * ((cap.numerator : ℝ) / cap.denominator) ^ 2) *
          (539 / 1000)))) ^ rows := by
  exact CertifiedJL.ternaryAffineLInfThresholdLower_probability_le rows cap
    (33 / 10) (97 / 200) (5 / 2) (539 / 1000)
    (sparseThresholdDiffuseWrappedRowBound_marginThree_of_replay
      CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
      CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
      CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified)
    (ThresholdDiffuseFloor73.wrappedRowBound_marginThree_of_replay
      CertificateProviders.sparseL2ThresholdDiffuseFloor73Endpoints_verified)
    hcap (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    q d w b shift hq hcentered hb hnorm hmargin

end CertifiedJL.Results.Affine.LInf.Lower.Direct
