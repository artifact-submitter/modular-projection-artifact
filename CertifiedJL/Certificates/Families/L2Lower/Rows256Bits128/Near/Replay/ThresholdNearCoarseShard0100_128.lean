/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0100_00_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0100_01_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0100_10_128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearCoarseShard0100_11_128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0100_check : planCheck cell0100 shardPlan0100 = true := by
  simp only [shardPlan0100, cell01000, cell01001, cell010000, cell010001,
    cell010010, cell010011, planCheck, Bool.and_eq_true]
  exact ⟨⟨shard0100_00_check, shard0100_01_check⟩,
    ⟨shard0100_10_check, shard0100_11_check⟩⟩

end CertifiedJL.ThresholdNearCoarse128
