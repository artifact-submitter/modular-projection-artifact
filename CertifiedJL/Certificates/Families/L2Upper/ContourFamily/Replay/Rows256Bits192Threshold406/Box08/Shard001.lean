/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      87097428319962560808215677166208231059228759944365763061197960348358022323170511191593783482627798732544270035704169129583441267⟩ := by
  decide +kernel

theorem box_08_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      9104731299833369471330325922413148282901019317282971113484710523800860352516330806716626264935167154008865227959986860411890461062673964650601113234288⟩ := by
  decide +kernel

theorem box_08_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      41133526722941944252619839816405830028248402325533262068847920589500420707472009322866318723496673039007477850857562943353338247502467202896749425204077⟩ := by
  decide +kernel

theorem box_08_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      450641557254252812523883529511231425604382667400228962234582142405288200465881828699773521685937005719628906593226202851083223265427749550032830966163⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
