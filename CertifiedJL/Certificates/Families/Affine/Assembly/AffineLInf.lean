/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Soundness.LInfNumeric
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.Affine
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Provider128

/-! # Shared assembly of the first direct affine infinity lower tails -/

namespace CertifiedJL.CertificateAssembly

/-- Direct affine cap `67/200` at 256 rows and 130 bits, under margin three. -/
theorem affineLInfCap67Over200
    (scalar : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (tail : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    (high : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128) :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 67, denominator := 200, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 130) := by
  apply ternaryAffineLInfThresholdLowerTail_of_wrappedRowBound
    256 130 _ (33 / 10) (97 / 200)
    (sparseThresholdDiffuseWrappedRowBound_marginThree_of_replay scalar tail high)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using AffineLInfNumeric.cap67Over200_ratio

/-- Direct affine cap `6/25` at 256 rows and 197 bits, under margin three. -/
theorem affineLInfCap6Over25
    (scalar : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (tail : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    (high : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128) :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 6, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 197) := by
  apply ternaryAffineLInfThresholdLowerTail_of_wrappedRowBound
    256 197 _ (33 / 10) (97 / 200)
    (sparseThresholdDiffuseWrappedRowBound_marginThree_of_replay scalar tail high)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using AffineLInfNumeric.cap6Over25_ratio

end CertifiedJL.CertificateAssembly
