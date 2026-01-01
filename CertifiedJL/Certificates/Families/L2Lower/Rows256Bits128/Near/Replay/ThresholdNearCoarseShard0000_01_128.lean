/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_01_00_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_01_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_01_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_01_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0000_01_check :
    planCheck cell000001 shardPlan0000_01 = true := by
  simp only [shardPlan0000_01, cell0000010, cell0000011, cell00000100,
    cell00000101, cell00000110, cell00000111, planCheck, Bool.and_eq_true]
  exact ⟨⟨shard0000_01_00_check, shard0000_01_01_check⟩,
    ⟨shard0000_01_10_check, shard0000_01_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
