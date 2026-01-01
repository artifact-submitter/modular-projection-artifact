/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 10.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_10_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      745826227405621132947421283375419368546149909410976608766339672194125642247891873757802581859491671325129299515588080474226211904139305668461808584675927⟩ := by
  decide +kernel

theorem box_10_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      955716716772264247917980213823929709200927096609513835337229575320798715900830897644470927232726⟩ := by
  decide +kernel

theorem box_10_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      14335111634985941694439107190587754565⟩ := by
  decide +kernel

theorem box_10_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      78588390520122088478630941660829298767345217776425460293575050160218229349705199904595565483931337913051911459922889135832253988442114499739067486761978⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
