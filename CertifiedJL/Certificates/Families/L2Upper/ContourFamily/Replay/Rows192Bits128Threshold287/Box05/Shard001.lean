/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      869079825120531584684044863384037583838258230863509021493647316419745313206238324563193697941510187756111668080357614118804337199244954721⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      6470877204052981021500549186098595115508834097297769550747709881356902161791806089758373675269607651062345039371997791259213742421498⟩ := by
  decide +kernel

theorem box_05_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      110297923132206088774884182423909948375347393967132155917032989628770735312450011982918806787802948740142496935677177506057779340⟩ := by
  decide +kernel

theorem box_05_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      376341363770441657154204107487926373021893075169839620155150504288894728139895616130509322648618202457174328456114292449⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
