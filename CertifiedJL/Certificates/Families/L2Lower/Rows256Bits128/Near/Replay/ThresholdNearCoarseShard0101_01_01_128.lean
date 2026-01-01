/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_00_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_0100_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_0101_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_0110_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_0111_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_01_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0101_01_01_check :
    planCheck cell01010101 shardPlan0101_01_01 = true := by
  simp only [shardPlan0101_01_01, shardPlan0101_01_01LowerRight,
    cell010101010, cell010101011, cell0101010100, cell0101010101,
    cell0101010110, cell0101010111, cell01010101010, cell01010101011,
    cell010101010100, cell010101010101, cell010101010110,
    cell010101010111, planCheck, Bool.and_eq_true]
  exact
    ⟨⟨shard0101_01_01_00_check,
        ⟨⟨shard0101_01_01_0100_check, shard0101_01_01_0101_check⟩,
          ⟨shard0101_01_01_0110_check, shard0101_01_01_0111_check⟩⟩⟩,
      ⟨shard0101_01_01_10_check, shard0101_01_01_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
