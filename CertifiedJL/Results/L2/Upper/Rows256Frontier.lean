/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Instances.Rows256RescaledFrontier.Provider
import CertifiedJL.Statements.Transport.ParameterMonotonicity
import CertifiedJL.Statements.Transport.Rows

/-! # Exact rational 256-row upper-tail frontier -/

namespace CertifiedJL.Results.L2.Upper.Rows256Frontier

open SparseUpperContourFamily.Instances.Rows256RescaledFrontier

/-- Every listed anchor has its exact rational threshold and power-of-two budget. -/
theorem certifiedEndpoint (endpoint : Endpoint)
    (hendpoint : endpoint ∈ certifiedEndpoints) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := endpoint.threshold }
      (failureTarget (parameters endpoint).securityBits) :=
  CertificateAssembly.ternaryL2UpperOfRows256RescaledEndpoint endpoint
    (threshold_ge_338 hendpoint)
    (CertificateProviders.sparseL2UpperContourRows256RescaledFrontier_verified
      endpoint hendpoint)

/-- Select any exact rational threshold and exact failure budget weakened from
one certified anchor.  This performs no interpolation between anchors. -/
theorem ofCertifiedEndpoint
    (anchor : Endpoint) (hanchor : anchor ∈ certifiedEndpoints)
    (threshold : NonnegativeRatio) (budget : ENNReal)
    (hthreshold : anchor.threshold.LE threshold)
    (hbudget : failureTarget (parameters anchor).securityBits ≤ budget) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := threshold }
      budget :=
  (certifiedEndpoint anchor hanchor).mono_parameters (by rfl) hthreshold hbudget

/-- Derive any power-of-two endpoint dominated by one listed anchor.

Compared with `ofCertifiedEndpoint`, this selector also permits row
restriction and accepts the target security level directly.  It adds no
numerical certificate and does not replay the shared contour cells. -/
theorem ofCertifiedEndpointAtBits
    (anchor : Endpoint) (hanchor : anchor ∈ certifiedEndpoints)
    (rows bits : ℕ) (threshold : NonnegativeRatio)
    (hrows : rows ≤ 256)
    (hthreshold : anchor.threshold.LE threshold)
    (hbits : bits ≤ (parameters anchor).securityBits) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := rows
        threshold := threshold }
      (failureTarget bits) :=
  (certifiedEndpoint anchor hanchor).mono_parameters
    hrows hthreshold (failureTarget_antitone hbits)

theorem ternaryL2Upper5623Over16Bits140 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨5623, 16, by decide⟩ }
      (failureTarget 140) := by
  simpa [bits140Threshold5623Over16, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits140Threshold5623Over16 (by simp [certifiedEndpoints])

theorem ternaryL2Upper5641Over16Bits141 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨5641, 16, by decide⟩ }
      (failureTarget 141) := by
  simpa [bits141Threshold5641Over16, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits141Threshold5641Over16 (by simp [certifiedEndpoints])

theorem ternaryL2Upper5659Over16Bits142 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨5659, 16, by decide⟩ }
      (failureTarget 142) := by
  simpa [bits142Threshold5659Over16, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits142Threshold5659Over16 (by simp [certifiedEndpoints])

theorem ternaryL2Upper5677Over16Bits143 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨5677, 16, by decide⟩ }
      (failureTarget 143) := by
  simpa [bits143Threshold5677Over16, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits143Threshold5677Over16 (by simp [certifiedEndpoints])

theorem ternaryL2Upper2847Over8Bits144 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨2847, 8, by decide⟩ }
      (failureTarget 144) := by
  simpa [bits144Threshold2847Over8, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits144Threshold2847Over8 (by simp [certifiedEndpoints])

theorem ternaryL2Upper357Bits145 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := NonnegativeRatio.ofNat 357 }
      (failureTarget 145) := by
  simpa [bits145Threshold357, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits145Threshold357 (by simp [certifiedEndpoints])

theorem ternaryL2Upper2865Over8Bits146 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨2865, 8, by decide⟩ }
      (failureTarget 146) := by
  simpa [bits146Threshold2865Over8, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits146Threshold2865Over8 (by simp [certifiedEndpoints])

theorem ternaryL2Upper1437Over4Bits147 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨1437, 4, by decide⟩ }
      (failureTarget 147) := by
  simpa [bits147Threshold1437Over4, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits147Threshold1437Over4 (by simp [certifiedEndpoints])

theorem ternaryL2Upper5765Over16Bits148 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨5765, 16, by decide⟩ }
      (failureTarget 148) := by
  simpa [bits148Threshold5765Over16, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits148Threshold5765Over16 (by simp [certifiedEndpoints])

theorem ternaryL2Upper5783Over16Bits149 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨5783, 16, by decide⟩ }
      (failureTarget 149) := by
  simpa [bits149Threshold5783Over16, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits149Threshold5783Over16 (by simp [certifiedEndpoints])

theorem ternaryL2Upper5801Over16Bits150 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨5801, 16, by decide⟩ }
      (failureTarget 150) := by
  simpa [bits150Threshold5801Over16, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits150Threshold5801Over16 (by simp [certifiedEndpoints])

theorem ternaryL2Upper2909Over8Bits151 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨2909, 8, by decide⟩ }
      (failureTarget 151) := by
  simpa [bits151Threshold2909Over8, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits151Threshold2909Over8 (by simp [certifiedEndpoints])

theorem ternaryL2Upper1459Over4Bits152 :
    L2UpperTailAt
      { distribution := .balancedTernary, rows := 256
        threshold := ⟨1459, 4, by decide⟩ }
      (failureTarget 152) := by
  simpa [bits152Threshold1459Over4, parameters,
    SparseUpperContourFamily.Parameters.securityBits] using
    certifiedEndpoint bits152Threshold1459Over4 (by simp [certifiedEndpoints])

end CertifiedJL.Results.L2.Upper.Rows256Frontier
