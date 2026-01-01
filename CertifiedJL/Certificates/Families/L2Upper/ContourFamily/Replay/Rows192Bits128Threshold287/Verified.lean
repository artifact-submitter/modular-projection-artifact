/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Data
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box00
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box01
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box02
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box03
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box04
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box05
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box06
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box07
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box08
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.Box09
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.HighProfile

/-! Aggregate kernel-verified endpoints for one upper-contour family instance. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def verifiedEndpoints :
    List (UpperContourKernel.DInterval (CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters).precision) :=
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Data.expectedBounds

theorem boxBounds_eq_verifiedEndpoints :
    (CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).map (boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters) =
      verifiedEndpoints := by
  change [
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default),
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
  ] = [
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box00.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box01.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box02.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box03.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box04.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box05.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box06.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box07.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box08.expectedBound,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows192Bits128Threshold287.Box09.expectedBound
  ]
  rw [CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box00Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box01Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box02Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box03Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box04Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box05Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box06Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box07Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box08Bound_eq_expected,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box09Bound_eq_expected]

theorem allBoxesCheck_eq_true :
    allBoxesCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes = true := by
  change ([
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default),
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
  ]).all id = true
  simp only [CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box00Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box01Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box02Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box03Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box04Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box05Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box06Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box07Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box08Check_eq_true,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified.box09Check_eq_true]
  rfl

theorem box_upperRat_lt_target {box : ProfileBox}
    (hbox : box ∈ CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes) :
    (boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters box).upperRat < box.target := by
  simp only [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes, List.mem_cons, List.not_mem_nil,
    or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box00_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box01_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box02_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box03_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box04_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box05_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box06_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box07_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box08_upperRat_lt
  · simpa [CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes] using box09_upperRat_lt

theorem highProfileCheck_eq_true :
    highProfileCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile = true :=
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.HighProfile.check_eq_true

theorem highProfile_upperRat_lt :
    (highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile).upperRat <
      CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile.target :=
  CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.HighProfile.upperRat_lt

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.Verified
