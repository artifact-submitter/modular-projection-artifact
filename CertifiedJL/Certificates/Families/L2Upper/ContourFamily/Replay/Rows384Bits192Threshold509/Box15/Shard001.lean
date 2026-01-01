/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 15.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_15_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      77710554783491555303406103122800372440888138159461422766255351109647082646352790713706541651343936435939906301163602171243087035673⟩ := by
  decide +kernel

theorem box_15_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      637452425185822744293801836646536243494744715438062380955111756539492105322724644486373062438211972402530118600106579838714⟩ := by
  decide +kernel

theorem box_15_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      57456667677550437811598875072440337984905709562861482310820799661395418842873926461064077056968428446693820014439015⟩ := by
  decide +kernel

theorem box_15_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      1367195393416096030899090783957171472005834025827552383154448868116611934457852381013732265927790531173587315⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
