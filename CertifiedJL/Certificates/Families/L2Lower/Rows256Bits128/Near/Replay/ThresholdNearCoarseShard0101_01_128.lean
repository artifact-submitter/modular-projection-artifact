/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_00_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0101_01_check :
    planCheck cell010101 shardPlan0101_01 = true := by
  simp only [shardPlan0101_01, cell0101010, cell0101011, cell01010100,
    cell01010110, cell01010111, planCheck, Bool.and_eq_true]
  exact ⟨⟨shard0101_01_00_check, shard0101_01_01_check⟩,
    ⟨shard0101_01_10_check, shard0101_01_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
