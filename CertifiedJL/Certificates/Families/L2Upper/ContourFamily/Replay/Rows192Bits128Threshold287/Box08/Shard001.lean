/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      454466785194476718376250873338917699098497937795321950074362504106398005502793252963078176545894418662373130792419475270020583046416124571755⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      30234021262702660656694118269133766272074017701411186805006689024201789205418846651358407290953007435547195302180490431714783774657445503⟩ := by
  decide +kernel

theorem box_08_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      15221589408997326783825793427297802554302197483875721397192749804963287362324405313081772390828742545223644773267745638191499161963898⟩ := by
  decide +kernel

theorem box_08_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      39968155182695803758639170662405178536885022090668384535292575687981793670636598914529388733328844055284226986635932244122110730726217⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
