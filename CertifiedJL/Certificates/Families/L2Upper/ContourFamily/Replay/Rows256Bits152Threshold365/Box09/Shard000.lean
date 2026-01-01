/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      211839613335614590636083771637859750317571450281887176322103596111228251940551562085501224595031124816770409172252991281814975436376673970890814909257485⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      6227750749730894321067980060720536936488798418261062269908458710177516213759239714432166567057178218240580850445214041633733772119405679367466631869821⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      28774393552391397522971200951649521330966030997614072827714119517370300259131039722951316069977431014574740344683712589927802976200606612617087870⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      4417483657948626856196162335641669057740155484807813350920547881971328144161909593992884330607845356504866699665695763156452101120265931134⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
