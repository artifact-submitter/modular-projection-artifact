/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0000_check : planCheck cell0000 shardPlan0000Final = true := by
  simp only [shardPlan0000Final, cell00001,
    cell000010, cell000011, planCheck, Bool.and_eq_true]
  exact ⟨⟨shard0000_00_check, shard0000_01_check⟩,
    ⟨shard0000_10_check, shard0000_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
