/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      655618774821732827123729434218577563891589394955194894402555595698587487659947311015555268997723940114063024612721955722948563537529777192181133672092788⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      13084787374211751940963896840088687574708349866506895996730077758182164724032949799635464105653513157427325315886407112550922874280570562409703665274369⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4308642684407938864019031982990966350835279447699139611217023780873761007402368070966251567667761448449971651636433353668572263724059170697712851812⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      91865255726059560458582465684045196487641809923103185419604571294793708058211073537758784527447883715991727096316244698364528371206609205341107⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
