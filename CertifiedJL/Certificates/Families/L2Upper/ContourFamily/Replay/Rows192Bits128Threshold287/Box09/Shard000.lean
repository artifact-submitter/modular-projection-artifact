/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      147903267403596631870892963221047669936249134804661646161935834555373842226548724312389900875000539998048329665818093228216875199866701037030206633769779⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      114976834970592482079587583042539046676923230632195354252121775737801619293209474449433643969106030424664261926035152480360451940213831741304409644716053⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3436700947732300531882314648757895090273940348459389126778493670708058373551349845322934654882797483273918966567914322004359963376186803079286732910326⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      2481884588271060236417998044637097852707907188132354806761203474750338295773583108846559434299869293928197191535138566526536148758715883236629047333⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
