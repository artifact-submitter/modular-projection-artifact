/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 30.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_30_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 30 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      385331119018374863071430830079761542774024060866629324827957562181636893755861979146000847756719821381732675939528219869753394194585014459882206074047261⟩ := by
  decide +kernel

theorem box_30_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 30 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      71856589065563799151531893521868006344319974977010897067040668799409013549675489251291572128446168⟩ := by
  decide +kernel

theorem box_30_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 30 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      36517546118559375456273817560472038051218281825911957665137749161436436822428487406572052961293709367212504132696284079251775592491694849523307312703619⟩ := by
  decide +kernel

theorem box_30_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 30 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      61986291287138703304476958182645947722801683906198773294224654089125224745696381096503868191959439595806951951956811092304400047927944735178889694565108⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
