/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordCurvatureCover128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearChordEndpointsVerified128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseVerified128

/-! # Narrow verified near-profile providers shared by centered and affine tails -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdNearCoarseCover128_verified :
    CertificateContracts.SparseL2ThresholdNearCoarseCover128 :=
  ThresholdNearCoarse128.semanticEnvelope_lt_543_div_1000

theorem sparseL2ThresholdNearEndpoints128_verified :
    CertificateContracts.SparseL2ThresholdNearEndpoints128 where
  fourFifths :=
    ThresholdNearChord128.semanticEnvelope_lt_endpointCap128_at_fourFifths
  seventeenTwentieths :=
    ThresholdNearChord128.semanticEnvelope_lt_endpointCap128_at_seventeenTwentieths
  nineTenths :=
    ThresholdNearChord128.semanticEnvelope_lt_endpointCap128_at_nineTenths
  nineteenTwentieths :=
    ThresholdNearChord128.semanticEnvelope_lt_endpointCap128_at_nineteenTwentieths
  one := ThresholdNearChord128.semanticEnvelope_lt_endpointCap128_at_one

theorem sparseL2ThresholdNearCurvature128_verified :
    CertificateContracts.SparseL2ThresholdNearCurvature128 :=
  ThresholdNearChordCurvature128.semanticChordCentralSecond_gt_neg_81_div_20

end CertifiedJL.CertificateProviders
