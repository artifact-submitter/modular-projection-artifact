/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.L2.Upper.Rows256Frontier

/-! # Focused API and axiom checks for the 256-row upper frontier -/

namespace CertifiedJL.Tests.Rows256UpperFrontier

#check Results.L2.Upper.Rows256Frontier.certifiedEndpoint
#check Results.L2.Upper.Rows256Frontier.ofCertifiedEndpoint
#check L2UpperTailAt.mono_parameters
#check Results.L2.Upper.Rows256Frontier.ofCertifiedEndpointAtBits
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5623Over16Bits140
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5641Over16Bits141
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5659Over16Bits142
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5677Over16Bits143
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper2847Over8Bits144
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper357Bits145
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper2865Over8Bits146
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper1437Over4Bits147
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5765Over16Bits148
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5783Over16Bits149
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5801Over16Bits150
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper2909Over8Bits151
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper1459Over4Bits152

open SparseUpperContourFamily.Instances.Rows256RescaledFrontier in
example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 192
        threshold := NonnegativeRatio.ofNat 365 }
      (failureTarget 152) := by
  apply Results.L2.Upper.Rows256Frontier.ofCertifiedEndpointAtBits
    bits152Threshold1459Over4 (by simp [certifiedEndpoints])
  · omega
  · norm_num [bits152Threshold1459Over4, NonnegativeRatio.ofNat,
      NonnegativeRatio.LE]
  · norm_num [parameters, bits152Threshold1459Over4,
      SparseUpperContourFamily.Parameters.securityBits]

open SparseUpperContourFamily.Instances.Rows256RescaledFrontier in
example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 240
        threshold := NonnegativeRatio.ofNat 360 }
      (failureTarget 147) := by
  apply Results.L2.Upper.Rows256Frontier.ofCertifiedEndpointAtBits
    bits147Threshold1437Over4 (by simp [certifiedEndpoints])
  · omega
  · norm_num [bits147Threshold1437Over4, NonnegativeRatio.ofNat,
      NonnegativeRatio.LE]
  · norm_num [parameters, bits147Threshold1437Over4,
      SparseUpperContourFamily.Parameters.securityBits]

open SparseUpperContourFamily.Instances.Rows256RescaledFrontier in
example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 358 }
      (failureTarget 145) := by
  apply Results.L2.Upper.Rows256Frontier.ofCertifiedEndpointAtBits
    bits145Threshold357 (by simp [certifiedEndpoints])
  · omega
  · norm_num [bits145Threshold357, NonnegativeRatio.ofNat,
      NonnegativeRatio.LE]
  · norm_num [parameters, bits145Threshold357,
      SparseUpperContourFamily.Parameters.securityBits]

open Lean in
run_cmd
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name := #[
    ``CertifiedJL.L2UpperTailAt.mono_parameters,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.certifiedEndpoint,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ofCertifiedEndpoint,
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ofCertifiedEndpointAtBits,
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
    ``CertifiedJL.Results.L2.Upper.Rows256Frontier.ternaryL2Upper1459Over4Bits152]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == standard.size && axioms.all standard.contains &&
        standard.all axioms.contains do
      throwError "unexpected frontier axiom footprint for {target}: {axioms}"

end CertifiedJL.Tests.Rows256UpperFrontier
