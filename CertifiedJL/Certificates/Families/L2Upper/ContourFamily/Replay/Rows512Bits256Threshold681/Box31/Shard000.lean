/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 31.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_31_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 31 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      308779520881493233943152326454261152983671311894205814633690093430694358141311373698516264235913437411420062837563469022301771071146609899019239217215390⟩ := by
  decide +kernel

theorem box_31_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 31 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      18528236836593455275443158606008110323073762934427136568029110409430427273816028786181408924554535994⟩ := by
  decide +kernel

theorem box_31_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 31 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      88831185846489212337239921282081260513501942397243596865356009814357105069509342004699894428332877536068406925621586740557439321811286988640237947239270⟩ := by
  decide +kernel

theorem box_31_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 31 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      13178656505383049416240154111657366956605722356246865937953253336377317460456988365020179558799125501697841862152180888340743122964842077323806296485597⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
