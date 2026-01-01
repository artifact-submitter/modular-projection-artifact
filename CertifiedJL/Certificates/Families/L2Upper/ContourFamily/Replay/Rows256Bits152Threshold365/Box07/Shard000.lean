/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      377665490194817458688161229690892635343268360963791236273143466862336135656501702987893564531999125493718807798525140903672700195085002395549655876914861⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      459277880562421974538294683307717329588880455353868863590425926884455431097002462902086891267258363161562664330618879374211134868436880995178222952529⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      102963533521704754961092002302113781946245890407742884207936414707985517524355454683270863312552957559617221141832026637495657689513253719336239⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      382178300177165433298304528925650809815108657542790660302847816211534101548556362156142462604342313218056664866366860013810003868806214⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
