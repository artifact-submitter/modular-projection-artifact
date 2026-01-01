/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box00
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box01
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box03
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box04
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box05
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box06
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box07
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box08
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box09
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box10
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box11
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box12
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box13
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box14
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box15
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box16

/-! Untrusted generated endpoints; `Verified` replays every chunk in the kernel. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Data

set_option linter.style.longLine false

def generatorRevision : String := "high-security-upper-contour-configs-v1"
def precision : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).precision
def rows : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).rows
def securityBits : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).securityBits
def threshold : ℚ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).threshold
def boxCount : ℕ := 17
def chunkCounts : List ℕ := [
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12,
    12
  ]

def chunks : List (List (Interval precision)) :=
  [
    Box00.chunks,
    Box01.chunks,
    Box02.chunks,
    Box03.chunks,
    Box04.chunks,
    Box05.chunks,
    Box06.chunks,
    Box07.chunks,
    Box08.chunks,
    Box09.chunks,
    Box10.chunks,
    Box11.chunks,
    Box12.chunks,
    Box13.chunks,
    Box14.chunks,
    Box15.chunks,
    Box16.chunks
  ]

def expectedBounds : List (Interval precision) :=
  [
    Box00.expectedBound,
    Box01.expectedBound,
    Box02.expectedBound,
    Box03.expectedBound,
    Box04.expectedBound,
    Box05.expectedBound,
    Box06.expectedBound,
    Box07.expectedBound,
    Box08.expectedBound,
    Box09.expectedBound,
    Box10.expectedBound,
    Box11.expectedBound,
    Box12.expectedBound,
    Box13.expectedBound,
    Box14.expectedBound,
    Box15.expectedBound,
    Box16.expectedBound
  ]

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Data
