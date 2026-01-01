/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.SparseUpperContourFamilyFixture

/-! Kernel replay shard 0 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default)
      ⟨0, 0, 1⟩ =
      ⟨0,
      549755813888⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default)
      ⟨0, 1, 1⟩ =
      ⟨0,
      490772077525⟩ := by
  decide +kernel


end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay
