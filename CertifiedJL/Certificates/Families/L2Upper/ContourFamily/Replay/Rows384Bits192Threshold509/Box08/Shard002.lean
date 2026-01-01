/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      1209110716640927214304617823740870403855007324988820928452771632788235486188177⟩ := by
  decide +kernel

theorem box_08_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      2939073775805339289087068794138908642916522333579186946188346122776⟩ := by
  decide +kernel

theorem box_08_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      40447923929314599622676468302943900204742681111670888027019889572658916570595858337140369743172445172769693956613836508518343072024261122226406944589559⟩ := by
  decide +kernel

theorem box_08_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      204119382647305755172306160531669329450009230002245408452703683743279989072448860969562034107616539285789325871564472651958190847330354563012029099330⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
