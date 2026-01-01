/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      59134186164173020098978453856150977531447459174150671861173403604400130190146072299147760900348685481670295226649475881414053953⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      31211704426813775020402385182465309258630000289755473423818896840077064995934953369907537291150542982999332834400895963⟩ := by
  decide +kernel

theorem box_06_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      34678602905240308630666661754431860752882059200799569912316963558808150274080199492181416689724767471302682282⟩ := by
  decide +kernel

theorem box_06_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      467896665046730551235714593360085300059737949397913394385406115610490657998419048762481513458⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
