/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_00_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0101_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0101_check : planCheck cell0101 shardPlan0101Final = true := by
  simp only [shardPlan0101Final, cell01010, cell01011, cell010100,
    cell010110, cell010111, planCheck, Bool.and_eq_true]
  exact ⟨⟨shard0101_00_check, shard0101_01_check⟩,
    ⟨shard0101_10_check, shard0101_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
