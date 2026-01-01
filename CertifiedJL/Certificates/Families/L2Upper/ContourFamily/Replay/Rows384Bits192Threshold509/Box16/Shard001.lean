/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 16.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_16_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      895468529226146032295930451790179757826871869048181643465358157066840988785278892813172461893718749394277943048604138598524249570629846⟩ := by
  decide +kernel

theorem box_16_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      292898951995703044237744142906764375725912522049145452072878355263769384016679043138736471371356304048240505383992510278530059878⟩ := by
  decide +kernel

theorem box_16_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      11098403778144062012454165416324262845515155942833697137943935236525139611683585907102986949858348735744407400079986605164773⟩ := by
  decide +kernel

theorem box_16_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      808084687328218430170321626753090025791628589674488409648615231144840069029457006092440056898660262200125513233959156155947535002032332380514⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
