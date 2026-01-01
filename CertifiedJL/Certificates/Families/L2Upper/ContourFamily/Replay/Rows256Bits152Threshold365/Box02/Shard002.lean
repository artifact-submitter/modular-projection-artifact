/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 2 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨4, 0, 10⟩ =
      ⟨0,
      506818540043703896254657622528185019846657162596096575324322768282976435227528781724947467630837480561458416944605140200206267244871009849810252168471⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
