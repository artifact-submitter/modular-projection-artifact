/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0001_0000_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0001_0001_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0001_0010_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0001_0011_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0001_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0001_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0001_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0001_check : planCheck cell0001 shardPlan0001 = true := by
  simp only [shardPlan0001, shardPlan0001LowerLeft, cell00010, cell00011,
    cell000100, cell000101, cell000110, cell000111, cell0001000,
    cell0001001, cell00010000, cell00010001, cell00010010, cell00010011,
    planCheck, Bool.and_eq_true]
  exact
    ⟨⟨⟨⟨shard0001_0000_check, shard0001_0001_check⟩,
          ⟨shard0001_0010_check, shard0001_0011_check⟩⟩,
        shard0001_01_check⟩,
      ⟨shard0001_10_check, shard0001_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
