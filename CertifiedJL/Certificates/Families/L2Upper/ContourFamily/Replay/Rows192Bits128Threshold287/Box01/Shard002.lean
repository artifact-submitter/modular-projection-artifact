/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      607585041796212660524460138980681279215824415829108883412932202982547964878598974206297172020405935537858364919⟩ := by
  decide +kernel

theorem box_01_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      912607595351828955786676266568658175575508078683350733251410106215722006005122084294787824889300676626644⟩ := by
  decide +kernel

theorem box_01_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      131174567154069406652460848270037941495923560270184177447710100273866641801143332153011318584782615720847192961722666584670797434499355131538223963998015⟩ := by
  decide +kernel

theorem box_01_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      2040346486090765819651205226248640439803370717015917926425871261150965452454266424241249655500500275832595405056702847340662518564389398950677631220328⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
