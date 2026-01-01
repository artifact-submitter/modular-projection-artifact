/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarsePartition128

namespace CertifiedJL.ThresholdNearCoarse128

theorem shard0001_0000_check :
    planCheck cell00010000 (shardPlan0001DeepChild cell00010000) = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearCoarse128
