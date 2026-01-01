/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01

/-! Untrusted generated endpoints; `Verified` replays every chunk in the kernel. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Data

set_option linter.style.longLine false

def generatorRevision : String := "fixture-v3-box-shards"
def precision : ℕ := (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).precision
def rows : ℕ := (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).rows
def securityBits : ℕ := (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).securityBits
def threshold : ℚ := (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).threshold
def boxCount : ℕ := 2
def chunkCounts : List ℕ := [
    2,
    3
  ]

def chunks : List (List (Interval precision)) :=
  [
    Box00.chunks,
    Box01.chunks
  ]

def expectedBounds : List (Interval precision) :=
  [
    Box00.expectedBound,
    Box01.expectedBound
  ]

end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Data
