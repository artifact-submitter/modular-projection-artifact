/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      171001217882727042819580138618493468893079000591655550082825402002863423824188463908652422504629527492126211501284369443132293079⟩ := by
  decide +kernel

theorem box_08_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      230516500688099632486858049245249903320958711348963605288298423835769162731658144890597679030893648429229079600693446412026717368104476⟩ := by
  decide +kernel

theorem box_08_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      136497267251256847186469104147210105420372580556567172318925515062697798577497213841638510541098660963545362456496263463376360510144548629087038598671827⟩ := by
  decide +kernel

theorem box_08_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      1145226534366908784108389768907079270298228255042564432221256084209424775630837592377602076815936702768927959867045301268460676710427525849634559036334⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
