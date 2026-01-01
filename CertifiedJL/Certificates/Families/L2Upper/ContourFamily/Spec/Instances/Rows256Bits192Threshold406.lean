/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Common

/-!
# The 256-row, 192-bit, threshold-406 upper-contour instance

This source instance transcribes the corresponding positive configuration in
`verify_high_security_upper_contour_configs.py`. It contains data only; the
analytic soundness module supplies the semantic contour proofs separately.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily.Instances

def parameters : Parameters where
  precision := 512
  rowOddPart := 1
  rowSquareCount := 8
  securityBlockBits := 12
  securityScaleSquarings := 4
  threshold := 406

def profileBoxes : List ProfileBox :=
  [ profileBox 0 (1 / 1024) (1717 / 2500) (104 / 125) (383 / 1000) mesh180,
    profileBox (1 / 1024) (1 / 512) (11 / 16) 1 (179 / 1000) mesh180,
    profileBox (1 / 512) (3 / 1024) (6881 / 10000) (223 / 200)
      (6 / 125) mesh180,
    profileBox (3 / 1024) (1 / 256) (3443 / 5000) (299 / 250) 0 mesh180,
    profileBox (1 / 256) (3 / 512) (861 / 1250) (1307 / 1000) 0 mesh180,
    profileBox (3 / 512) (1 / 128) (431 / 625) (1383 / 1000) 0 mesh180,
    profileBox (1 / 128) (1 / 64) (3447 / 5000) (1601 / 1000) 0 mesh180,
    profileBox (1 / 64) (3 / 128) (3463 / 5000) (1631 / 1000) 0 mesh180,
    profileBox (3 / 128) (1 / 32) (3489 / 5000) (803 / 500) 0 mesh180,
    profileBox (1 / 32) (1 / 20) (7031 / 10000) (729 / 500) 0 mesh180 ]

def highProfile : HighProfileBox where
  profileMinimum := 1 / 20
  lam := 363 / 500
  target := 1

theorem rows_eq : parameters.rows = 256 := by decide
theorem securityBits_eq : parameters.securityBits = 192 := by decide
theorem profileBoxCount_eq : profileBoxes.length = 10 := by decide
theorem cellCount_eq : familyCellCount profileBoxes = 1800 := by decide
theorem chunkCount_eq : familyChunkCount profileBoxes = 90 := by decide
theorem replayShardCount_eq : familyReplayShardCount 4 profileBoxes = 30 := by decide

end CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406
