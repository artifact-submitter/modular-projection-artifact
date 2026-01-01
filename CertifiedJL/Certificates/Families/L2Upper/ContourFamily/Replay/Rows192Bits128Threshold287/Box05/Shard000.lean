/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      583220827760971308200929494213868611374579766881578780287287006393554390049853911098867724753291570784500103400497686962012065646337358548696386618250480⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      12816426652209958940371672844542407781960822456980888412221990646784320307856231149278959394411509824412111963245480991126419788399729894767747860764777⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4857902805364919209397804974732388180680327762067937514225632887863150936058049216110857651296168636961526334809942761467831936774470714116667713283⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      115651808790888537005418620527358917717589703348252037457586074504695267695598874303833844010352425667062387332953817367965265103045562677544873⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
