/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      59626788477919768140395380201001772509414771236229932410205902862468640806651782344717618043330419775049233203841646506240799639⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      31799214501948796882869790165298535688667631427281283508279777999441934925011501871495195872476141706364900188867486302⟩ := by
  decide +kernel

theorem box_01_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      35525100372940397371449978626923133074056204105435336348008946100955686011635131686261091827393819950501523128⟩ := by
  decide +kernel

theorem box_01_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      457007512930139766682901535993645804484795570450235758965013971604151783719407670584932351274⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
