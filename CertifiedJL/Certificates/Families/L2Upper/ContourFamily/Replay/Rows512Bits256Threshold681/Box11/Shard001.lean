/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 1 for box 11.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_11_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 11 default)
      ⟨4, 0, 3⟩ =
      ⟨0,
      30112310183037663785564866629519302630052130695729133481498454612487628733121546382093287337776783577016066854044051345562480556001951216573835552556954⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
