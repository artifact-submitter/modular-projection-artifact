/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 1 for box 34.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_34_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 34 default)
      ⟨4, 0, 3⟩ =
      ⟨0,
      5723404286638379645854872091397658116381985885178113234323643326565560870412660646308149413662352251861581949349838556816098731323576231612368⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
