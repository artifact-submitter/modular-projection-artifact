/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 1 for box 17.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_17_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 17 default)
      ⟨4, 0, 3⟩ =
      ⟨0,
      22170947187685758054945075319071392667311276448941924747509565561926317607810531938154460712451255818795074483621325116286502619699121392456920419667613⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
