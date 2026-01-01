/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      10530145443710029973948134600307623994327681638410051130473434107138561076062272705527130796305036110389749024372474209732959⟩ := by
  decide +kernel

theorem box_01_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      488549757418503474106764213858717744756861429163301003018318897941423371282548165045470274845559736893157517⟩ := by
  decide +kernel

theorem box_01_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      337788596565560009209886266472424942298894645485383238934126249606920799976968310376406524194103⟩ := by
  decide +kernel

theorem box_01_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      87144209997102019110619792639224581721731283229764814664132797696026063372723475436379867202723759817262984034565722889837481758069925881904047512339827⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
