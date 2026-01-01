/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      633356081881460619017362405332417969999723784828062041662066044566831861730279⟩ := by
  decide +kernel

theorem box_02_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      364737114840121343610799455246324171627710601741749807631260123746⟩ := by
  decide +kernel

theorem box_02_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      26376094167459356035414842423622344707307088359265770744904138617821355219144076933645812017932670059863290964424061793571354320205151543976106427490564⟩ := by
  decide +kernel

theorem box_02_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      28919577945971961658768518257007429036783603588227722056830446131407347784128986689026297492713116786879032181778206777456869842313039429722590712952335⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
