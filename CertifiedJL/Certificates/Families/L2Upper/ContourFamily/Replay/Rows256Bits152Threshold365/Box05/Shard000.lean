/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      639203730778009529817667835964816949117278319375360378576146545295254763734791623448351347435151256281979584163240891785161846044093835722144153254402555⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      265746883316572426144157746657351036679910067938603929714355387435013717523652364904052055705094320727190285023461454779820843135222959456064276009088⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      15336421792523794483876987470909061171025384539056167020383267467002181771015276859053880842444376154662138637426047886877439157104309800200119⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      15498383770896534829952090925780406310709105591297731361359904462855186482739844065176885691803915372711512336874286715759303904085069⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
