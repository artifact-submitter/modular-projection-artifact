/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 22.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_22_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 22 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      687748662895892202541942032414211564340197239842710879061153178525175715824384566433938264489920567125354387721074991502730680770983199061202622919151953⟩ := by
  decide +kernel

theorem box_22_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 22 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      4172715911503030457772313998131949059936869151636493899388869935686918203672574349152633283966956⟩ := by
  decide +kernel

theorem box_22_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 22 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      543627833043689449587401592995636281759⟩ := by
  decide +kernel

theorem box_22_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 22 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      178664829297441036403350236600587510566673095322134164816416804121240126820164640534381301386749136141893199674355050795291174038578738075287420511497931⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
