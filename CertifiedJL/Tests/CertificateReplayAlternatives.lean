/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.ElementaryCore
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ConstantNumeric
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseCover128
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.CrossingCore
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.OuterPlan
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Soundness
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Final
import CertifiedJL.Tests.UpperContourShortTailBudgets
import CertifiedJL.Tests.LInfIntegerIdentity
import CertifiedJL.Tests.TaylorExp
import CertifiedJL.Tests.UpperHybridBudgets
import CertifiedJL.Tests.ContourConstantCoreBudgets
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.SignedClosedCore
import CertifiedJL.Tests.Rows384Bits192Threshold509SignedClosedCore
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.ClosedCoreFirstBox

/-! Fast checks of alternative replay soundness, without expensive leaf imports. -/

open CertifiedJL.TrigonometricBernstein

open Lean in
run_cmd
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name := #[
    ``CertifiedJL.SparseUpperContourFamily.SignedClosedCore.rowMajorant_le_signedGaussian,
    ``CertifiedJL.SparseUpperContourFamily.coreSubstitutedBoxSound_of_budget,
    ``CertifiedJL.SparseUpperContourFamily.integral_Ioc_actualBoxQuadratureIntegrand_le_halfGaussianOfExpEnvelope,
    ``CertifiedJL.SparseUpperContourFamily.ConstantCoreExperiment.three_suffix_geometries,
    ``CertifiedJL.Tests.Rows384Bits192Threshold509SignedClosedCore.box02_rowMajorant,
    ``CertifiedJL.Tests.Rows384Bits192Threshold509SignedClosedCore.box08_rowMajorant,
    ``CertifiedJL.SparseUpperHybrid.BudgetTests.all_eighteen_targets,
    ``CertifiedJL.SparseUpperContourFamily.ConstantCoreExperiment.three_original_targets,
    ``CertifiedJL.SparseUpperContour.ClosedCore.leading_modulus_le,
    ``CertifiedJL.SparseUpperContour.ClosedCore.rowMajorant_le_closedGaussian,
    ``CertifiedJL.SparseUpperContour.ClosedCore.firstBox_core_integral_lt,
    ``CertifiedJL.SparseUpperContour.ClosedCore.integral_Ioc_actualBoxQuadratureIntegrand_le_coarseRectangles,
    ``CertifiedJL.SparseUpperContour.ClosedCore.firstBox_coarse_closed_endpoint_of_budget,
    ``CertifiedJL.TaylorExp.negUpper_contains,
    ``CertifiedJL.TaylorExp.posUpper_contains,
    ``affinePullbackQ_eq_bernsteinPolynomialQ_of_integerCertificate,
    ``CertifiedJL.TrigonometricBernstein.IntegerIdentityTests.original_rational_identity,
    ``CertifiedJL.SparseUpperContour.ShortTail.tail_integral_le,
    ``CertifiedJL.SparseUpperContour.ShortTail.endpoint_lt,
    ``CertifiedJL.SparseUpperContour.ShortTail.normalized607_of_contract,
    ``CertifiedJL.SparseUpperContour.ShortTailExperiment.all_ten_original_targets,
    ``CertifiedJL.Probability.tyurinCoreIntegral_le_closed,
    ``CertifiedJL.TyurinModerate.cellCertified_of_closedCore,
    ``CertifiedJL.Probability.tyurinCoreIntegral_le_crossingClosed,
    ``CertifiedJL.TyurinModerate.cellCertified_of_crossingCore,
    ``CertifiedJL.TyurinModerate.outerIntegral_le_outerPlan,
    ``CertifiedJL.TyurinModerate.cellCertified_of_coreIntegralBound_outerPlan,
    ``CertifiedJL.TyurinModerate.cellCertified_of_closedCore_outerPlan,
    ``CertifiedJL.TyurinModerate.cellCertified_of_crossingCore_outerPlan,
    ``CertifiedJL.SparseThresholdDominant.ConstantNumeric.localCertifiedGeometricCheckAt_sound,
    ``CertifiedJL.SparseThresholdDominant.ConstantNumeric.localCertifiedGeometricCheckFor_sound,
    ``CertifiedJL.SparseThresholdDominant.ConstantNumeric.rowCapsCheck_sound,
    ``CertifiedJL.SparseThresholdDominant.ConstantNumeric.all_rowCapsCheck_of_eq,
    ``CertifiedJL.SparseThresholdDominant.ConstantNumeric.all_localCertifiedCheckFor_of_rowCaps,
    ``CertifiedJL.SparseThresholdDominant.ConstantNumeric.localCertifiedCheckAt_sound,
    ``CertifiedJL.SparseThresholdDominant.ConstantNumeric.localCertifiedCheckFor_sound,
    ``CertifiedJL.ThresholdNearCoarse128.semanticEnvelope_lt_of_planCheck]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.all standard.contains do
      throwError "unexpected replay-alternative axiom footprint for {target}: {axioms}"
