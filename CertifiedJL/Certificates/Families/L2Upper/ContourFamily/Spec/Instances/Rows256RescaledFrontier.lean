/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365
import CertifiedJL.Statements.Shared.ExactRatio

/-! # Rescaled 256-row upper-contour endpoints

The expensive quadrature integral depends on the row count and the profile
partition, but not on the security scale or tail threshold.  These endpoint
records keep those reusable fields fixed while exposing the two parameters
that change along the 256-row frontier.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows256RescaledFrontier

open CertifiedJL.SparseUpperContourFamily.Instances

/-- Exact parameters that vary along the fixed 256-row contour profile. -/
structure Endpoint where
  securityBlockBits : ℕ
  securityScaleSquarings : ℕ
  threshold : CertifiedJL.NonnegativeRatio
deriving DecidableEq, Repr

/-- Interpret an exact nonnegative threshold as a rational contour input. -/
def thresholdRat (endpoint : Endpoint) : ℚ :=
  endpoint.threshold.numerator / endpoint.threshold.denominator

/-- Contour parameters with the expensive 256-row/profile portion fixed. -/
def parameters (endpoint : Endpoint) : Parameters where
  precision := 512
  rowOddPart := 1
  rowSquareCount := 8
  securityBlockBits := endpoint.securityBlockBits
  securityScaleSquarings := endpoint.securityScaleSquarings
  threshold := thresholdRat endpoint

abbrev profileBoxes : List ProfileBox :=
  Rows256Bits152Threshold365.profileBoxes

abbrev highProfile : HighProfileBox :=
  Rows256Bits152Threshold365.highProfile

def bits140Threshold352 : Endpoint :=
  ⟨35, 2, CertifiedJL.NonnegativeRatio.ofNat 352⟩

def bits140Threshold5623Over16 : Endpoint :=
  ⟨35, 2, ⟨5623, 16, by decide⟩⟩

def bits141Threshold5641Over16 : Endpoint :=
  ⟨141, 0, ⟨5641, 16, by decide⟩⟩

def bits142Threshold5659Over16 : Endpoint :=
  ⟨71, 1, ⟨5659, 16, by decide⟩⟩

def bits143Threshold5677Over16 : Endpoint :=
  ⟨143, 0, ⟨5677, 16, by decide⟩⟩

def bits144Threshold356 : Endpoint :=
  ⟨18, 3, CertifiedJL.NonnegativeRatio.ofNat 356⟩

def bits144Threshold2847Over8 : Endpoint :=
  ⟨18, 3, ⟨2847, 8, by decide⟩⟩

def bits145Threshold357 : Endpoint :=
  ⟨145, 0, CertifiedJL.NonnegativeRatio.ofNat 357⟩

def bits146Threshold2865Over8 : Endpoint :=
  ⟨73, 1, ⟨2865, 8, by decide⟩⟩

def bits147Threshold1437Over4 : Endpoint :=
  ⟨147, 0, ⟨1437, 4, by decide⟩⟩

def bits148Threshold361 : Endpoint :=
  ⟨37, 2, CertifiedJL.NonnegativeRatio.ofNat 361⟩

def bits148Threshold5765Over16 : Endpoint :=
  ⟨37, 2, ⟨5765, 16, by decide⟩⟩

def bits149Threshold5783Over16 : Endpoint :=
  ⟨149, 0, ⟨5783, 16, by decide⟩⟩

def bits150Threshold363 : Endpoint :=
  ⟨75, 1, CertifiedJL.NonnegativeRatio.ofNat 363⟩

def bits150Threshold5801Over16 : Endpoint :=
  ⟨75, 1, ⟨5801, 16, by decide⟩⟩

def bits151Threshold364 : Endpoint :=
  ⟨151, 0, CertifiedJL.NonnegativeRatio.ofNat 364⟩

def bits151Threshold2909Over8 : Endpoint :=
  ⟨151, 0, ⟨2909, 8, by decide⟩⟩

def bits152Threshold365 : Endpoint :=
  ⟨19, 3, CertifiedJL.NonnegativeRatio.ofNat 365⟩

def bits152Threshold1459Over4 : Endpoint :=
  ⟨19, 3, ⟨1459, 4, by decide⟩⟩

/-- The exact rational anchors replayed by the compact frontier checker. -/
def certifiedEndpoints : List Endpoint :=
  [ bits140Threshold5623Over16,
    bits141Threshold5641Over16,
    bits142Threshold5659Over16,
    bits143Threshold5677Over16,
    bits144Threshold2847Over8,
    bits145Threshold357,
    bits146Threshold2865Over8,
    bits147Threshold1437Over4,
    bits148Threshold5765Over16,
    bits149Threshold5783Over16,
    bits150Threshold5801Over16,
    bits151Threshold2909Over8,
    bits152Threshold1459Over4 ]

theorem threshold_ge_338 {endpoint : Endpoint}
    (hendpoint : endpoint ∈ certifiedEndpoints) :
    338 ≤ (parameters endpoint).threshold := by
  simp only [certifiedEndpoints, List.mem_cons, List.not_mem_nil, or_false] at hendpoint
  rcases hendpoint with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [parameters, thresholdRat, bits140Threshold5623Over16,
      bits141Threshold5641Over16, bits142Threshold5659Over16,
      bits143Threshold5677Over16, bits144Threshold2847Over8,
      bits145Threshold357, bits146Threshold2865Over8,
      bits147Threshold1437Over4, bits148Threshold5765Over16,
      bits149Threshold5783Over16, bits150Threshold5801Over16,
      bits151Threshold2909Over8, bits152Threshold1459Over4,
      CertifiedJL.NonnegativeRatio.ofNat]

theorem rows_eq (endpoint : Endpoint) : (parameters endpoint).rows = 256 := by
  norm_num [parameters, Parameters.rows]

theorem threshold_toReal (endpoint : Endpoint) :
    endpoint.threshold.toReal = ((parameters endpoint).threshold : ℝ) := by
  simp [CertifiedJL.NonnegativeRatio.toReal, parameters, thresholdRat]

end CertifiedJL.SparseUpperContourFamily.Instances.Rows256RescaledFrontier
