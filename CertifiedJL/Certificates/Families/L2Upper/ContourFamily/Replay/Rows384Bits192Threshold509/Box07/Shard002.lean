/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      891864783079441614520351291536257154801292922615065921644157503737831103354106⟩ := by
  decide +kernel

theorem box_07_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      1304292088240588496358069460397206678075173749111346346047732208129⟩ := by
  decide +kernel

theorem box_07_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      54595653752635816549309500783446661997175628126203481782909640786028024867523321215071980821925744166580554759890583245152209040673035499967476902738739⟩ := by
  decide +kernel

theorem box_07_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      1233338193403080038253320606241972072172468279720220595261732451821922818434098209649240131955644468070572106991321290543491194472316238658803486311854⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
