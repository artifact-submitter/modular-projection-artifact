/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box00
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box02
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box03
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box04
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box05
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box06
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box07
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box08
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box09
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box11
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box12
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box13
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box14
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box15
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box16
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box17
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box19
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box20
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box21
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box22
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box23
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box25
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box26
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box27
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box28
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box29
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box30
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box31
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box32
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box33
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box34

/-! Untrusted generated endpoints; `Verified` replays every chunk in the kernel. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Data

set_option linter.style.longLine false

def generatorRevision : String := "high-security-upper-contour-configs-681-v1"
def precision : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision
def rows : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).rows
def securityBits : ℕ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).securityBits
def threshold : ℚ := (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).threshold
def boxCount : ℕ := 35
def chunkCounts : List ℕ := [
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5,
    5
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
    Box16.chunks,
    Box17.chunks,
    Box18.chunks,
    Box19.chunks,
    Box20.chunks,
    Box21.chunks,
    Box22.chunks,
    Box23.chunks,
    Box24.chunks,
    Box25.chunks,
    Box26.chunks,
    Box27.chunks,
    Box28.chunks,
    Box29.chunks,
    Box30.chunks,
    Box31.chunks,
    Box32.chunks,
    Box33.chunks,
    Box34.chunks
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
    Box16.expectedBound,
    Box17.expectedBound,
    Box18.expectedBound,
    Box19.expectedBound,
    Box20.expectedBound,
    Box21.expectedBound,
    Box22.expectedBound,
    Box23.expectedBound,
    Box24.expectedBound,
    Box25.expectedBound,
    Box26.expectedBound,
    Box27.expectedBound,
    Box28.expectedBound,
    Box29.expectedBound,
    Box30.expectedBound,
    Box31.expectedBound,
    Box32.expectedBound,
    Box33.expectedBound,
    Box34.expectedBound
  ]

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Data
