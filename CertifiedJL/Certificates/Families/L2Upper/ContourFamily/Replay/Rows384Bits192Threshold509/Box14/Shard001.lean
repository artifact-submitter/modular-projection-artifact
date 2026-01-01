/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 14.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_14_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      5392798705692157364233815870770286474049384886908568520674634511564369095782998455493548644885883406639871344468481834821039484340⟩ := by
  decide +kernel

theorem box_14_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      14911086423391441664161052122051569766049355859347847420968922906191340070502279618886498390985339715155358494838386171155⟩ := by
  decide +kernel

theorem box_14_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      224143261847876987346708418307632851487084192507014678234069588117873388477814815227189541556802230734949642599560⟩ := by
  decide +kernel

theorem box_14_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      120922800634829341781335853878823057704635897350283705295840330359594087704369540388157506489521204282⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
