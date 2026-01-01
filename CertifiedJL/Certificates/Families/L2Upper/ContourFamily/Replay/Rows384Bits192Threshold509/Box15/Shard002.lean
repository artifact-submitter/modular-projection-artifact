/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 15.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_15_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      3174557416330705344121235821553389725411516222302643089448493067946124793436667302668730835610436568615375505803456872703664686⟩ := by
  decide +kernel

theorem box_15_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      33547166059642233459883273202722474148981725786374816084172467124502396009360786013931054240722773470760014382437987996430852411491491824296335488571745⟩ := by
  decide +kernel

theorem box_15_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      278979275696815999009156463047169355942814468180694029870726516277736600681022835655629102453337596547893341224337106055014391347018046834951459755353⟩ := by
  decide +kernel

theorem box_15_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      6604561421926759052058855310378757316881558310118969226398681010456340271626249054116740687466101335670966940244286573638291997483629959465431⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
