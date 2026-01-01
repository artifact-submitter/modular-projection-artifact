/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      1841387622042245325175147097739066719341704004020515293548544937725077445770118⟩ := by
  decide +kernel

theorem box_09_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      8231325537054485014691900861027327843845439082969759791075753088561⟩ := by
  decide +kernel

theorem box_09_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      52764373107341787673258515616906318306826481211047721709535844573685327733504845299348011561477821312452938339566242298992329897183600402179329987443368⟩ := by
  decide +kernel

theorem box_09_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      192147793640268556255033988932495006340864640726256647992355181935915524774618612847908627493177064108101196565043052876280632419077162778653090051022⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
