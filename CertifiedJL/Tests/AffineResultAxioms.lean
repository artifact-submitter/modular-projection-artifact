/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.Transports.Rows
import CertifiedJL.Results.Affine.L2.Lower.Endpoints
import CertifiedJL.Results.Affine.LInf.Lower.Endpoints
import CertifiedJL.Results.Affine.L2.Upper
import CertifiedJL.Results.Affine.LInf.Upper
import CertifiedJL.Results.Affine.LInf.Lower.MarginTwo
import CertifiedJL.Results.Affine.LInf.Lower.Direct

/-! # Standard axiom checks for every concrete affine endpoint -/

open Lean in
run_cmd
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name := #[
    ``CertifiedJL.Results.Transports.Rows.ternaryL2Upper195Threshold338Bits128,
    ``CertifiedJL.Results.Transports.Rows.ternaryAffineL2Upper195Threshold338Bits128,
    ``CertifiedJL.Results.Transports.Rows.ternaryL2Upper264Threshold509Bits128,
    ``CertifiedJL.Results.Transports.Rows.ternaryAffineL2Upper264Threshold509Bits128,
    ``CertifiedJL.Results.Transports.Rows.ternaryL2Upper394Threshold607Bits192,
    ``CertifiedJL.Results.Transports.Rows.ternaryAffineL2Upper394Threshold607Bits192,
    ``CertifiedJL.Results.Transports.Rows.ternaryLInfUpper462Cap1358Over100Bits197,
    ``CertifiedJL.Results.Transports.Rows.ternaryAffineLInfUpper462Cap1358Over100Bits197,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower192Floor11Bits128,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower256Floor27Bits128,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower256Floor9Bits194,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower384Floor40Bits192,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower512Floor73Bits193,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower512Floor54Bits256,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower195Floor12Bits128,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower264Floor29Bits128,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower394Floor43Bits192,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower524Floor57Bits256,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower192Cap279Over1000Bits129,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower256Cap331Over1000Bits133,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower384Cap331Over1000Bits200,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower512Cap331Over1000Bits266,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower512Cap46Over125Bits206,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower256Cap9Over25Bits109,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower462Cap9Over25Bits197,
    ``CertifiedJL.Results.Affine.L2.Lower.Endpoints.allL2LowerBounds,
    ``CertifiedJL.Results.Affine.LInf.Lower.Endpoints.allLInfLowerBounds,
    ``CertifiedJL.Results.Affine.L2.Upper.ternaryAffineL2Upper192Threshold287Bits128,
    ``CertifiedJL.Results.Affine.LInf.Upper.ternaryAffineLInfUpper192Cap487Over50Bits128,
    ``CertifiedJL.Results.Affine.L2.Upper.ternaryAffineL2Upper256Threshold338Bits128,
    ``CertifiedJL.Results.Affine.L2.Upper.ternaryAffineL2Upper512Threshold607Bits192,
    ``CertifiedJL.Results.Affine.LInf.Upper.ternaryAffineLInfUpper256Cap39Over4Bits133,
    ``CertifiedJL.Results.Affine.LInf.Upper.ternaryAffineLInfUpper256Cap1181Over100Bits192,
    ``CertifiedJL.Results.Affine.LInf.Upper.ternaryAffineLInfUpper384Cap1183Over100Bits192,
    ``CertifiedJL.Results.Affine.LInf.Upper.ternaryAffineLInfUpper512Cap1184Over100Bits192,
    ``CertifiedJL.Results.Affine.LInf.Upper.ternaryAffineLInfUpper512Cap1358Over100Bits256,
    ``CertifiedJL.Results.Affine.L2.Upper.ternaryAffineL2Upper256Threshold406Bits192,
    ``CertifiedJL.Results.Affine.L2.Upper.ternaryAffineL2Upper384Threshold509Bits192,
    ``CertifiedJL.Results.Affine.L2.Upper.ternaryAffineL2Upper512Threshold681Bits256,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower192Cap93Over500Margin2Bits129,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap4Over25Margin2Bits197,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap331Over1500Margin2Bits133,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower384Cap331Over1500Margin2Bits200,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower512Cap331Over1500Margin2Bits266,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower512Cap92Over375Margin2Bits206,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap67Over300Margin2Bits130,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap6Over25Margin2Bits109,
    ``CertifiedJL.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower462Cap6Over25Margin2Bits197,
    ``CertifiedJL.Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130,
    ``CertifiedJL.Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == standard.size && axioms.all standard.contains &&
        standard.all axioms.contains do
      throwError "unexpected affine-result axiom footprint for {target}: {axioms}"

#print axioms CertifiedJL.Results.Transports.Rows.allRowRestrictedUpperEndpoints
