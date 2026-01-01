/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.SignedClosedCore
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-!
# Exact signed-core witnesses for the 384-row threshold-509 profile

These bounded examples show that the reusable signed endpoint conditions apply
to both an easy and a tight production profile box.  The numerical endpoint
budget comparison remains a diagnostic, not a theorem in this file.
-/

namespace CertifiedJL.Tests.Rows384Bits192Threshold509SignedClosedCore

open Set
open SparseUpperContourFamily
open SparseUpperContourFamily.SignedClosedCore
open SparseUpperContourFamily.Instances
open SparseUpperContourFamily.Instances.Rows384Bits192Threshold509

/-- The two literal witnesses below are tied to the current production boxes,
and their first fifty production cells cover exactly `[0, 1/6]`. -/
theorem production_box_fields_and_first_fifty_cells :
    let box02 := profileBoxes.getD 2 default
    let box08 := profileBoxes.getD 8 default
    box02.profileLeft = 1 / 2048 ∧
    box02.profileRight = 3 / 4096 ∧
    box02.lam = 6251 / 10000 ∧
    box08.profileLeft = 1 / 512 ∧
    box08.profileRight = 5 / 2048 ∧
    box08.lam = 6257 / 10000 ∧
    box02.segments = mesh285 ∧
    box08.segments = mesh285 ∧
    50 ≤ box02.segments.head!.count ∧
    50 ≤ box08.segments.head!.count ∧
    box02.segments.head!.cellLeft 0 = 0 ∧
    box02.segments.head!.cellRight 49 = 1 / 6 ∧
    box08.segments.head!.cellLeft 0 = 0 ∧
    box08.segments.head!.cellRight 49 = 1 / 6 := by
  decide +kernel

private theorem box02_left : EndpointConditions
    (1 / 2048) (6251 / 10000) (1 / 6)
    (323469 / 500000) (2725629 / 1000000) (55603 / 20000)
    (2780149 / 1000000) (113909347 / 1000000) (955913 / 1000000)
    (11049 / 500000) (1618763 / 1000000)
    (3101 / 20000000) (804167 / 500000) := by
  constructor <;> norm_num

private theorem box02_right : EndpointConditions
    (3 / 4096) (6251 / 10000) (1 / 6)
    (323469 / 500000) (2725629 / 1000000) (55603 / 20000)
    (2780149 / 1000000) (113909347 / 1000000) (955913 / 1000000)
    (3383 / 125000) (1618763 / 1000000)
    (3101 / 20000000) (804167 / 500000) := by
  constructor <;> norm_num

theorem box02_rowMajorant
    {profile frequency : ℝ}
    (hprofile : profile ∈ Icc (1 / 2048 : ℝ) (3 / 4096))
    (hfrequency : frequency ∈ Icc (0 : ℝ) (1 / 6)) :
    sparseUpperContourRowMajorant profile (6251 / 10000) frequency ≤
      Real.exp (-(3101 / 20000000 : ℝ) -
        (804167 / 500000 : ℝ) * frequency ^ 2) := by
  have hprofile' : profile ∈ Icc ((1 / 2048 : ℚ) : ℝ) ((3 / 4096 : ℚ) : ℝ) := by
    norm_num at hprofile ⊢
    exact hprofile
  have hfrequency' : frequency ∈ Icc (0 : ℝ) ((1 / 6 : ℚ) : ℝ) := by
    norm_num at hfrequency ⊢
    exact hfrequency
  convert (rowMajorant_le_signedGaussian (profile := profile) (frequency := frequency)
    (by norm_num) box02_left box02_right hprofile' hfrequency') using 1 <;> norm_num

private theorem box08_left : EndpointConditions
    (1 / 512) (6257 / 10000) (1 / 6)
    (323759 / 500000) (341243 / 125000) (2794427 / 1000000)
    (1397213 / 500000) (917621 / 8000) (955787 / 1000000)
    (8839 / 200000) (25367 / 15625)
    (56057 / 100000000) (1588483 / 1000000) := by
  constructor <;> norm_num

private theorem box08_right : EndpointConditions
    (5 / 2048) (6257 / 10000) (1 / 6)
    (323759 / 500000) (341243 / 125000) (2794427 / 1000000)
    (1397213 / 500000) (917621 / 8000) (955787 / 1000000)
    (49411 / 1000000) (25367 / 15625)
    (56057 / 100000000) (1588483 / 1000000) := by
  constructor <;> norm_num

/-- Tight diagnostic box 8: fifty production mesh cells lie below the proved
`1/6` cutoff. -/
theorem box08_rowMajorant
    {profile frequency : ℝ}
    (hprofile : profile ∈ Icc (1 / 512 : ℝ) (5 / 2048))
    (hfrequency : frequency ∈ Icc (0 : ℝ) (1 / 6)) :
    sparseUpperContourRowMajorant profile (6257 / 10000) frequency ≤
      Real.exp (-(56057 / 100000000 : ℝ) -
        (1588483 / 1000000 : ℝ) * frequency ^ 2) := by
  have hprofile' : profile ∈ Icc ((1 / 512 : ℚ) : ℝ) ((5 / 2048 : ℚ) : ℝ) := by
    norm_num at hprofile ⊢
    exact hprofile
  have hfrequency' : frequency ∈ Icc (0 : ℝ) ((1 / 6 : ℚ) : ℝ) := by
    norm_num at hfrequency ⊢
    exact hfrequency
  convert (rowMajorant_le_signedGaussian (profile := profile) (frequency := frequency)
    (by norm_num) box08_left box08_right hprofile' hfrequency') using 1 <;> norm_num

end CertifiedJL.Tests.Rows384Bits192Threshold509SignedClosedCore
