/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 13.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_13_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      344980967649008771621371922788285016520419184391771894629672290214981504904824621848037901726323727972271918685137644454531156438045352541604500741121745⟩ := by
  decide +kernel

theorem box_13_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1358118445300341222127770445882159634319854834498502534938252729699929716830157159683913652399499733202910197285692922740995886070133240053261409307165⟩ := by
  decide +kernel

theorem box_13_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      8499395351487460931480612265060821170261956463617147934332893978048099030821073032246893068525418370977094657449437202042433259885182670203346726⟩ := by
  decide +kernel

theorem box_13_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      319187925300935077410912996948087256102551830000232933823519208777477307953947237680276876376293079763312034355284885797952368656259194566⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
