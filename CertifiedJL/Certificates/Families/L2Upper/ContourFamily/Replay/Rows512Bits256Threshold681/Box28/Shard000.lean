/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 28.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_28_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 28 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      548193574633059100622299144885207534771458938464417207001174793537775739219017887284182445349708815337585136973187484976506345140061825749717707884846028⟩ := by
  decide +kernel

theorem box_28_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 28 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      4136857445675792854800961740900883455107618176547657729592846314077678332591988741991536299029171⟩ := by
  decide +kernel

theorem box_28_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 28 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      5446575803877545171376508245099818414470324214177641627461163774217170460⟩ := by
  decide +kernel

theorem box_28_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 28 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      159207362840421300770942746511422419604690468678816138154388400780524147691427888781357530741792756920611816693620883156531988843814759614856362836084906⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
