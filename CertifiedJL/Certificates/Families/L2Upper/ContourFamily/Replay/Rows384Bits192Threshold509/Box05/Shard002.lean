/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      728393114553443367274289778493081896938437512470658299938982555027441987475958⟩ := by
  decide +kernel

theorem box_05_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      684408419539233683873586906350792800261025378588678783042807861664⟩ := by
  decide +kernel

theorem box_05_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      58461990518328983694273719148785983221762598559342441174526375889063618946267248687671290375339241411044089069886271464570673914910723691561899957493714⟩ := by
  decide +kernel

theorem box_05_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      3648071020860634615579592165224550569050563646988143336062188361402798623582495433754732362258986370507417852091771104376900512936102064783182183496858⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
