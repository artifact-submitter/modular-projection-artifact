/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 10.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_10_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      3714720103261868225292802497573316801507468052802064560464834531062627374034311⟩ := by
  decide +kernel

theorem box_10_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      19767796092837777966696211310696089294452968616830565978656856059424033663406533119401248⟩ := by
  decide +kernel

theorem box_10_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      52280410098650699309315887794732913646411719416619830633185304030698821561239375317317526312986690084656379847142281275928331176391099485660840711115875⟩ := by
  decide +kernel

theorem box_10_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      40528738437034469201543979574900399313571088684314022546969908134036239465535941428599142184943138152671161159205392072514929504053745344932487858122⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
