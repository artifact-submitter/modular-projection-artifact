/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      661420189486063970076595992942449794254556213281034608512214256581049045910793061987152547439509048662985431466478685556881315742777686715768381303596735⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1912663098057883555219269217843622419508494265865470521759524638819420524639086981935426280938843243425754638437237720385589576464215648053878187621906⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4200292192620187715487594661261519749379351937153308470913925832639110931766966006791232660022711287604622385703979077212274604421650851254421014⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      56399728600622507587148964398749327915333231826875176327336818778272751063626299062915925008059149900753680718698680259283810465772075493⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
