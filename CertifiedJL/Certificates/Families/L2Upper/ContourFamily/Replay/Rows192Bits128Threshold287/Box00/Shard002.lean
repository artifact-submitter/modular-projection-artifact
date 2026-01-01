/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      404966862279456240744559209773590442368386219267069365804679587734263612845846580801201456322294013078276842330⟩ := by
  decide +kernel

theorem box_00_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      324478329138135499743705680388562760621622429047491409940629463791983132137920671247412181836756058835981⟩ := by
  decide +kernel

theorem box_00_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      102630630734423959541224740486819104004143432675826118149607843365877038386536319439610901215391408906667407490368402132142551567817033562008640057164788⟩ := by
  decide +kernel

theorem box_00_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      19493770622520606979129563593454560067138821035514097791301057844274107050669208226556896298317246987009391243539628440865473766861621635380441805573573⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
