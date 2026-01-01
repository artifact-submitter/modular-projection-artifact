/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 2 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨4, 0, 10⟩ =
      ⟨0,
      7172765568684238947349664098405375695632472895472224633711576813369043581016346901183535920567715367827442184785508671473932521617076276743973601797745⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
