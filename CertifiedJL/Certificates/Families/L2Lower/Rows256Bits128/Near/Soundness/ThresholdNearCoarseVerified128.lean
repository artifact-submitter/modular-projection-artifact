/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseAggregate128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseCover128

/-! # Verified exhaustive coarse cover for the 128-bit near band -/

namespace CertifiedJL
namespace ThresholdNearCoarse128

/-- The sixteen independently replayed shards, assembled in the same exact
binary partition used to define their cells. -/
def verifiedPlan : Plan :=
  .splitX
    (.splitA
      (.splitX
        (.splitA shardPlan0000Final shardPlan0001)
        (.splitA (shardPlan cell0010) (shardPlan cell0011)))
      (.splitX
        (.splitA shardPlan0100 shardPlan0101Final)
        (.splitA (shardPlan cell0110) (shardPlan cell0111))))
    (.splitA
      (.splitX
        (.splitA (shardPlan cell1000) (shardPlan cell1001))
        (.splitA (shardPlan cell1010) (shardPlan cell1011)))
      (.splitX
        (.splitA (shardPlan cell1100) (shardPlan cell1101))
        (.splitA (shardPlan cell1110) (shardPlan cell1111))))

private theorem verifiedPlan_check : planCheck rootCell verifiedPlan = true := by
  simp only [verifiedPlan, rootCell, cell0, cell1, cell00, cell01, cell10, cell11,
    cell001, cell011, cell100, cell101, cell110, cell111,
    cell0010, cell0011, cell0110, cell0111,
    cell1000, cell1001, cell1010, cell1011, cell1100, cell1101, cell1110, cell1111,
    planCheck, Bool.and_eq_true]
  exact
    ⟨⟨⟨⟨shard0000_check, shard0001_check⟩,
          ⟨shard0010_check, shard0011_check⟩⟩,
        ⟨⟨shard0100_check, shard0101_check⟩,
          ⟨shard0110_check, shard0111_check⟩⟩⟩,
      ⟨⟨⟨shard1000_check, shard1001_check⟩,
          ⟨shard1010_check, shard1011_check⟩⟩,
        ⟨⟨shard1100_check, shard1101_check⟩,
          ⟨shard1110_check, shard1111_check⟩⟩⟩⟩

/-- Uniform coarse-envelope bound on the complete normalized near band. -/
theorem semanticEnvelope_lt_543_div_1000
    {x a : ℝ}
    (hxLower : 1 ≤ x) (hxUpper : x ≤ 4901 / 2500)
    (haLower : 9 / 16 ≤ a) (haUpper : a ≤ 2401 / 2500) :
    semanticEnvelope x a < 543 / 1000 := by
  apply semanticEnvelope_lt_of_planCheck rootCell verifiedPlan
  · simpa [rootCell] using And.intro hxLower
      (And.intro hxUpper (And.intro haLower haUpper))
  · exact verifiedPlan_check

end ThresholdNearCoarse128
end CertifiedJL
