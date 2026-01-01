/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform
import CertifiedJL.Results.Affine.L2.Lower.General
import CertifiedJL.Results.L2.Lower.Rows256Bits128
import CertifiedJL.Results.L2.Upper.Rows256Bits128
import CertifiedJL.Results.L2.Upper.Rows256Frontier
import CertifiedJL.Results.Composites.L2Rows256Bits128
import CertifiedJL.Results.L2.Lower.Rows192Bits128
import CertifiedJL.Results.L2.Upper.Rows192Bits128
import CertifiedJL.Results.LInf.Lower.Rows192Bits128
import CertifiedJL.Results.LInf.Upper.Rows192Bits128
import CertifiedJL.Results.Composites.Rows192Bits128
import CertifiedJL.Results.L2.Lower.Rows256Bits152
import CertifiedJL.Results.L2.Lower.Rows256Bits192
import CertifiedJL.Results.L2.Upper.Rows256Bits192
import CertifiedJL.Results.LInf.Upper.Rows256Bits192
import CertifiedJL.Results.L2.Lower.Rows384Bits192
import CertifiedJL.Results.L2.Upper.Rows384Bits192
import CertifiedJL.Results.LInf.Upper.Rows384Bits192
import CertifiedJL.Results.L2.Upper.Rows512Bits192
import CertifiedJL.Results.LInf.Upper.Rows512Bits192
import CertifiedJL.Results.L2.Upper.Rows512Bits256
import CertifiedJL.Results.LInf.Upper.Rows512Bits256
import CertifiedJL.Results.L2.Lower.Rows512Bits192
import CertifiedJL.Results.L2.Lower.Rows512Bits193
import CertifiedJL.Results.L2.Lower.Rows512Bits256
import CertifiedJL.Results.L2.Lower.HighSecurity
import CertifiedJL.Results.LInf.Lower.HighSecurity
import CertifiedJL.Results.LInf.Upper.HighSecurity
import CertifiedJL.Results.LInf.Lower.TwoDecimal
import CertifiedJL.Obstructions

/-! # Exact axiom footprints of production results -/

open Lean in
run_cmd
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name := #[
    ``CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_finiteTilt,
    ``CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general,
    ``CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general_of_ratio,
    ``CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget,
    ``CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget,
    ``CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform.ternaryUpper39Over4,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29,
    ``CertifiedJL.Results.L2.Upper.Rows256Bits128.ternaryL2Upper338,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.certifiedEndpoint,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ofCertifiedEndpoint,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper5623Over16Bits140,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper5641Over16Bits141,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper5659Over16Bits142,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper5677Over16Bits143,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper2847Over8Bits144,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper357Bits145,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper2865Over8Bits146,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper1437Over4Bits147,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper5765Over16Bits148,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper5783Over16Bits149,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper5801Over16Bits150,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper2909Over8Bits151,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper1459Over4Bits152,
    ``CertifiedJL.Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12,
    ``CertifiedJL.Results.L2.Upper.Rows192Bits128.ternaryL2Upper287,
    ``CertifiedJL.Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50,
    ``CertifiedJL.Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50,
    ``CertifiedJL.Results.Composites.Rows192Bits128.allBounds,
    ``CertifiedJL.Results.LInf.Lower.TwoDecimal.rowPass21Over50_lt_13939Over20000,
    ``CertifiedJL.Results.LInf.Lower.TwoDecimal.lower6Over25Rows256Bits197,
    ``CertifiedJL.Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133,
    ``CertifiedJL.Results.LInf.Lower.TwoDecimal.lower21Over50Rows384Bits200,
    ``CertifiedJL.Results.LInf.Lower.TwoDecimal.lower21Over50Rows512Bits266,
    ``CertifiedJL.Results.LInf.Lower.TwoDecimal.lower47Over100Rows512Bits206,
    ``CertifiedJL.CertificateAssembly.affineL2RatioEndpoint,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.frontier_all_checked,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower79Over4Bits152,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower20Bits151,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower41Over2Bits150,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower83Over4Bits149,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower21Bits148,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower85Over4Bits147,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower43Over2Bits146,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower87Over4Bits145,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower22Bits144,
    ``CertifiedJL.Results.L2.Lower.Rows256Bits192.ternaryL2ThresholdLower9,
    ``CertifiedJL.Results.L2.Lower.Rows384Bits192.ternaryL2ThresholdLower43,
    ``CertifiedJL.Results.L2.Upper.Rows512Bits192.ternaryL2Upper607,
    ``CertifiedJL.Results.L2.Upper.Rows256Bits192.ternaryL2Upper406,
    ``CertifiedJL.Results.L2.Upper.Rows384Bits192.ternaryL2Upper509,
    ``CertifiedJL.Results.L2.Upper.Rows512Bits256.ternaryL2Upper681,
    ``CertifiedJL.Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower71,
    ``CertifiedJL.Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73,
    ``CertifiedJL.Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower73,
    ``CertifiedJL.Results.L2.Lower.Rows512Bits256.ternaryL2ThresholdLower57,
    ``CertifiedJL.Results.L2.Lower.HighSecurity.allLowerBounds,
    ``CertifiedJL.Results.L2.Lower.HighSecurity.allLowerBoundsIncluding256,
    ``CertifiedJL.Results.L2.Lower.HighSecurity.allLowerBoundsIncludingFloor73,
    ``CertifiedJL.Results.Composites.L2Rows256Bits128.allL2Bounds,
    ``CertifiedJL.Results.LInf.Upper.Rows256.ternaryLInfUpper39Over4Bits133,
    ``CertifiedJL.Results.LInf.Upper.Rows256.ternaryLInfUpper39Over4,
    ``CertifiedJL.Results.LInf.Upper.Rows256Bits192.ternaryLInfUpper1181Over100,
    ``CertifiedJL.Results.LInf.Upper.Rows384Bits192.ternaryLInfUpper1183Over100,
    ``CertifiedJL.Results.LInf.Upper.Rows512Bits192.ternaryLInfUpper1184Over100,
    ``CertifiedJL.Results.LInf.Upper.Rows512Bits256.ternaryLInfUpper1358Over100,
    ``CertifiedJL.Results.LInf.Lower.HighSecurity.allThresholdLowerBounds,
    ``CertifiedJL.Results.LInf.Upper.HighSecurity.allUpperBounds,
    ``CertifiedJL.ternaryUpper336Counterexample,
    ``CertifiedJL.ternaryUpper338Bits130Counterexample,
    ``CertifiedJL.ternaryL2UpperRows192Threshold287Bits130Counterexample,
    ``CertifiedJL.ternaryLInfUpperRows192Threshold487Over50Bits134Counterexample,
    ``CertifiedJL.thresholdLower512Bits192Floor76Counterexample,
    ``CertifiedJL.Obstructions.ternaryLInfRows256CoordinateCap1Bits128,
    ``CertifiedJL.Obstructions.ternaryLInfThresholdMarginOneBits130False,
    ``CertifiedJL.Obstructions.ternaryLInfThresholdMarginOneFamilyFalse,
    ``CertifiedJL.Obstructions.ternaryLInfThresholdRows192Cap34Bits183False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor30Bits128False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor30Margin125Bits128False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor29MarginAtMostNineFourthsBits128False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor29MarginTwoBits128False,
    ``CertifiedJL.Counterexamples.TernaryL2Rows256MarginTwo.admissible_family,
    ``CertifiedJL.Counterexamples.TernaryL2Rows256Floor30.admissible_witness,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor31Bits128False,
    ``CertifiedJL.Obstructions.ternaryL2SingletonThresholdFalseOfScaled,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows192Floor14Bits128False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor13Bits192False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows384Floor45Bits192False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows512Floor59Bits256False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor29Bits132False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor9Bits208False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows384Floor43Bits197False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows512Floor57Bits261False,
    ``CertifiedJL.Obstructions.ternaryLInfThresholdRows256CapHalfBits128False,
    ``CertifiedJL.Counterexamples.TernaryLInfRows256CapHalf.realMargin_admissible_family,
    ``CertifiedJL.Counterexamples.DenseSignThreshold.universal_real_threshold_failure,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows192Floor12Bits132False,
    ``CertifiedJL.Obstructions.ternaryL2UpperRows192Threshold287Bits130False,
    ``CertifiedJL.Obstructions.ternaryLInfUpperRows192Threshold487Over50Bits134False,
    ``CertifiedJL.Counterexamples.DenseSignThreshold.modularProjectionSqNorm_witness_le_rows,
    ``CertifiedJL.Obstructions.denseSignThreshold29FailsForEverySeed,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows512Bits192Floor76False,
    ``CertifiedJL.Obstructions.ternaryL2ThresholdRows512Bits192AtLeast76False]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == standard.size && axioms.all standard.contains &&
        standard.all axioms.contains do
      throwError "unexpected production-result axiom footprint for {target}: {axioms}"
