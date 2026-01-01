/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      699360343975461350794477830470620368997267676781951215261604161239188224306669059081709045290717144430463271376956881025717139624541539897118849340334704⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1997504627038377784848145507821600304587386562334068125463741468430242614555232868718688578355676353586351650334126369744485575957441266982478815251995⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4300706501494433880824820212091976543417890535480952860946367308907851099011633974853502271369207052846090843121552351128481831882559169733554016⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      57168204003176075102509089072135907279705020685985144721935921681329594279514262111797208416959658025156804266927459918306246884506898168⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
