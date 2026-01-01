/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      702751024168160651394777221930761338633571886455988090415874810363621489223742⟩ := by
  decide +kernel

theorem box_04_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      547891420501120495418639765761727610082113930280246641922176773274⟩ := by
  decide +kernel

theorem box_04_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      49506729626905129412065110750341466403358664906444439720367203154964735972807414206347379238487247164408758436627247130577841509770274888306923962265353⟩ := by
  decide +kernel

theorem box_04_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      6797518699106907804177054634571014902560567278999283990174323102406950438021710635357996557013695459550855638680967465155167024381778368157366804132184⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
