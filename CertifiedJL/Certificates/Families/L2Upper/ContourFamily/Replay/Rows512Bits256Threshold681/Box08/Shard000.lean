/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 8 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      759936953754026722047456882754567543406708189132436369131876359593385138722311498334468786292862376103570466669614379420544136266958159496953478109422843⟩ := by
  decide +kernel

theorem box_08_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 8 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1479255427492099741804053693637862507921114545427600167542062651743299927473299092683354148928537⟩ := by
  decide +kernel

theorem box_08_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 8 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      23652343455093638424744683704822347459⟩ := by
  decide +kernel

theorem box_08_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 8 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      154272451558417645999670561265000910660781795574676495367576209928763911044315553655129241586052132565892101960202135452522067272713923772038321871612184⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
