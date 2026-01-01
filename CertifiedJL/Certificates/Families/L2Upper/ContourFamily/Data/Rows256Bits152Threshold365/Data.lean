/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box00
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box01
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box02
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box03
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box04
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box05
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box06
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box07
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box08
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Box09

/-! Untrusted generated endpoints; `Verified` replays every chunk in the kernel. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Data

set_option linter.style.longLine false

def generatorRevision : String := "akita-rows256-bits152-threshold365-v1"
def precision : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters).precision
def rows : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters).rows
def securityBits : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters).securityBits
def threshold : ℚ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters).threshold
def boxCount : ℕ := 10
def chunkCounts : List ℕ := [
    9,
    9,
    9,
    9,
    9,
    9,
    9,
    9,
    9,
    9
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
    Box09.chunks
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
    Box09.expectedBound
  ]

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows256Bits152Threshold365.Data
