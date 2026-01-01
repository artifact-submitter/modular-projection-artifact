/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 2 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨4, 0, 10⟩ =
      ⟨0,
      926243099566374119199819812106325212381030359165331876507290267636753622697611796061866818486302441198913122075127570881363410972533032781893996514⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
