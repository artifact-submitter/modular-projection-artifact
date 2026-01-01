/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0000_00_check :
    planCheck cell000000 shardPlan0000_00 = true := by
  simp only [shardPlan0000_00, cell0000000, cell0000001,
    cell00000001, cell00000010, cell00000011, planCheck, Bool.and_eq_true]
  exact ⟨⟨shard0000_00_00_check, shard0000_00_01_check⟩,
    ⟨shard0000_00_10_check, shard0000_00_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
