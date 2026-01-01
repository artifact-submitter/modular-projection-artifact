/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      10405695771937468213916504633620971888588778912349557202335166063610644663887154089591532268328838460855621245596097302150628⟩ := by
  decide +kernel

theorem box_00_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      438052517031312156723980548724126027537886189205470261050859623616698109568255109821042476489451231450023632⟩ := by
  decide +kernel

theorem box_00_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      135011182744060687513197526251382371039236264901155199947723151644957844000161168047166210481224⟩ := by
  decide +kernel

theorem box_00_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      65362628444659806560968224002791981095551158039646538991086655106264006188313634660323232254627186570843227835226848139440160696714251617111078038140293⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
