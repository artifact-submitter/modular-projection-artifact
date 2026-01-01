/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 2 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨4, 0, 10⟩ =
      ⟨0,
      136129279029375912838381802445191917853129425810428413630872398960570648859300098879898921006729856834114582926614402986378010693765812383050263041⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
