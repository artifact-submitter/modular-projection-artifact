/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Numeric.Core

/-!
# Small fixture for the parameterized upper-contour replay generator

This is deliberately a plumbing fixture rather than a headline probability
claim.  It exercises multiple boxes, multiple segments, unequal segment
lengths, per-box chunk sizes, a replay shard crossing a segment boundary,
aggregate endpoint assembly, and the optional high-profile replay at
inexpensive precision.
-/

namespace CertifiedJL.Tests.SparseUpperContourFamilyFixture

open SparseUpperContourFamily

def parameters : Parameters where
  precision := 40
  rowOddPart := 0
  rowSquareCount := 1
  securityBlockBits := 0
  securityScaleSquarings := 0
  threshold := 100

def profileBoxes : List ProfileBox :=
  [ { profileLeft := 0
      profileRight := 1 / 4
      lam := 1 / 4
      sigma := 1 / 2
      theta := 0
      target := 1
      cutoff := 1 / 2
      segments := [⟨0, 1 / 8, 2⟩]
      chunkSize := 1 },
    { profileLeft := 1 / 4
      profileRight := 1 / 2
      lam := 1 / 3
      sigma := 2 / 3
      theta := 1 / 4
      target := 1
      cutoff := 1 / 2
      segments := [⟨0, 1 / 8, 1⟩, ⟨1 / 8, 1 / 8, 3⟩]
      chunkSize := 2 } ]

def highProfile : HighProfileBox where
  profileMinimum := 1 / 2
  lam := 1 / 3
  target := 1

end CertifiedJL.Tests.SparseUpperContourFamilyFixture
