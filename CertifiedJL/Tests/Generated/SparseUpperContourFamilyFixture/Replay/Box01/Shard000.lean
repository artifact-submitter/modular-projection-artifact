/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.SparseUpperContourFamilyFixture

/-! Kernel replay shard 0 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)
      ⟨0, 0, 1⟩ =
      ⟨0,
      412316860418⟩ := by
  decide +kernel

theorem box_01_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)
      ⟨1, 0, 2⟩ =
      ⟨0,
      710056015441⟩ := by
  decide +kernel


end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay
