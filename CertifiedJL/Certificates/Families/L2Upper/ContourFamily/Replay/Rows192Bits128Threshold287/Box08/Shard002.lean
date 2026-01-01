/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      6390766872273917535548933002233518676639364734866070298665126080551995471372898846247732001824438387058237786146564171445897136280517684748814139977⟩ := by
  decide +kernel

theorem box_08_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      118472404139035274365072053453744184472549571315924493590100709672695286331231905017338469628143619721032016067858344266954899879358701224073137322462064⟩ := by
  decide +kernel

theorem box_08_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      844933893486299691067503278433501909643316729720144387149269697646187517524809477210640535388210541528666527018398046660047943562876786775288070390381⟩ := by
  decide +kernel

theorem box_08_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      30874282428824327266422019101043738297202439111800882580892948955804016438457195215844503512935107582132986002493414315178200640295469609533573⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
