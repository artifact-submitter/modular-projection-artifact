/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      53824813680762243209542490833544038620590153188679819182425239244514329518962067702640611813239515558903084815238770086133740981903253934807634404327647⟩ := by
  decide +kernel

theorem box_09_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      63423375848528961078972404046484244434921810907355891283684863508803631078092134884192625710707761502938754075633681838355422859791689669552981804653757⟩ := by
  decide +kernel

theorem box_09_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      383481181534944503126390238918671674464230702081951806523649949139281502035384854379960099846396425328320282498296604197587499513815706401701621644289⟩ := by
  decide +kernel

theorem box_09_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      7329204253346898719110885811909529567566815937846810993756048731635522875419656433908982867676481072137052755054780968040619048407913456444778⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
