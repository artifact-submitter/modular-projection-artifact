/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      626945883801400258740620803559079795956503720755694332182092279134285996244488778449436367990082396295409846382477160665274183220711621401217500088612396⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1841637718221336527181423305444550547265729942132153117692247425450149892380880594407361560381859231765930856323405002183860191790362663271240040872948⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4151895185183341590838673726867202892451730389083266737680020377905768107140334385628434942792521620771655330339449279997199369128111487249511001⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      56791913257038745070038499919244505519168411420157767845659801189703406556291853403626562618193753990401328724277059786651289855151543285⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
