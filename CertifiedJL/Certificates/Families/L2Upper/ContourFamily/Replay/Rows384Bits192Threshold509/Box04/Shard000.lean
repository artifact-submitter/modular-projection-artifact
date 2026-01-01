/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      680182695873718649268118564576109419118591569744566150442653821501782149487096579411623189794228515481501784145365663239454294557020656871948686467621533⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1956891751074525787899673406025711309248426575502116666771344409245493157943129138041289561548524967585412679854965976464970722437830453891756580854653⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4267376517122181075117480282838082140475810036097978330075294345755047884154813857825010492679596206985708316349720444453640716821494844187917308⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      57208090351171762449852105641728489307597326684865971112094158739090649026969037923977040711260642622383107979228903355005072640689585700⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
