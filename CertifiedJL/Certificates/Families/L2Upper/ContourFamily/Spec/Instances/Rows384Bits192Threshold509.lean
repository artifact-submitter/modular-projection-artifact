/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Common

/-!
# The 384-row, 192-bit, threshold-509 upper-contour instance

This source instance transcribes the corresponding positive configuration in
`verify_high_security_upper_contour_configs.py`. It contains data only; the
analytic soundness module supplies the semantic contour proofs separately.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily.Instances

def parameters : Parameters where
  precision := 512
  rowOddPart := 3
  rowSquareCount := 7
  securityBlockBits := 12
  securityScaleSquarings := 4
  threshold := 509

def profileBoxes : List ProfileBox :=
  [ profileBox 0 (1 / 4096) (6249 / 10000) (269 / 500) (219 / 250) mesh285,
    profileBox (1 / 4096) (1 / 2048) (5 / 8) (16 / 25) (727 / 1000) mesh285,
    profileBox (1 / 2048) (3 / 4096) (6251 / 10000) (709 / 1000)
      (633 / 1000) mesh285,
    profileBox (3 / 4096) (1 / 1024) (1563 / 2500) (191 / 250)
      (563 / 1000) mesh285,
    profileBox (1 / 1024) (5 / 4096) (6253 / 10000) (809 / 1000)
      (253 / 500) mesh285,
    profileBox (5 / 4096) (3 / 2048) (1251 / 2000) (849 / 1000)
      (229 / 500) mesh285,
    profileBox (3 / 2048) (7 / 4096) (391 / 625) (221 / 250)
      (417 / 1000) mesh285,
    profileBox (7 / 4096) (1 / 512) (6257 / 10000) (183 / 200)
      (19 / 50) mesh285,
    profileBox (1 / 512) (5 / 2048) (6257 / 10000) (1021 / 1000)
      (131 / 500) mesh285,
    profileBox (5 / 2048) (3 / 1024) (6257 / 10000) (1021 / 1000)
      (131 / 500) mesh285,
    profileBox (3 / 1024) (1 / 256) (3131 / 5000) (138 / 125)
      (173 / 1000) mesh285,
    profileBox (1 / 256) (3 / 512) (1567 / 2500) (247 / 200)
      (37 / 1000) mesh285,
    profileBox (3 / 512) (1 / 128) (1569 / 2500) (661 / 500) 0 mesh285,
    profileBox (1 / 128) (1 / 64) (3139 / 5000) (309 / 200) 0 mesh285,
    profileBox (1 / 64) (3 / 128) (789 / 1250) (1647 / 1000) 0 mesh285,
    profileBox (3 / 128) (1 / 32) (793 / 1250) (1681 / 1000) 0 mesh285,
    profileBox (1 / 32) (1 / 20) (3187 / 5000) (849 / 500) 0 mesh285 ]

def highProfile : HighProfileBox where
  profileMinimum := 1 / 20
  lam := 82 / 125
  target := 1

theorem rows_eq : parameters.rows = 384 := by decide
theorem securityBits_eq : parameters.securityBits = 192 := by decide
theorem profileBoxCount_eq : profileBoxes.length = 17 := by decide
theorem cellCount_eq : familyCellCount profileBoxes = 4845 := by decide
theorem chunkCount_eq : familyChunkCount profileBoxes = 204 := by decide
theorem replayShardCount_eq : familyReplayShardCount 4 profileBoxes = 51 := by decide

end CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509
