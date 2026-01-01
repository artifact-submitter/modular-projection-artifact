/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      1720578185905047996953423271353711267880277401732707966249050670699764312883633080606737544213089564836588102482218234433⟩ := by
  decide +kernel

theorem box_06_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      144866895790490512680738125142405958204898221733272240154520921199738135926381450867708510961825576180793942292574601468860978159740029837043820937720046⟩ := by
  decide +kernel

theorem box_06_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      8001481764526606798414646215136115204085201622135611473170158326796442686593233990658081036035858578553164936044377794727537913437490055517348736810749⟩ := by
  decide +kernel

theorem box_06_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      4559713112756226936370017567575069181963594975396221033365188254966717641623817627451165662782398257383542406907648075719999347764322359831136772⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
