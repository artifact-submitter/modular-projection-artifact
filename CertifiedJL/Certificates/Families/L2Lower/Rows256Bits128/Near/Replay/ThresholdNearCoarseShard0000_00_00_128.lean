/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_0000_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_0001_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_0010_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_0011_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0000_00_00_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0000_00_00_check :
    planCheck cell00000000 shardPlan0000_00_00 = true := by
  simp only [shardPlan0000_00_00, shardPlan0000_00_00LowerLeft,
    cell000000000, cell000000001, cell0000000000, cell0000000001,
    cell0000000010, cell0000000011, cell00000000000, cell00000000001,
    cell000000000000, cell000000000001, cell000000000010,
    cell000000000011, planCheck, Bool.and_eq_true]
  exact
    ⟨⟨⟨⟨shard0000_00_00_0000_check, shard0000_00_00_0001_check⟩,
          ⟨shard0000_00_00_0010_check, shard0000_00_00_0011_check⟩⟩,
        shard0000_00_00_01_check⟩,
      ⟨shard0000_00_00_10_check, shard0000_00_00_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
