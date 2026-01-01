/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 23.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_23_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 23 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      681697168220880754829602286959432022746267744371331596081041666135170067676363527512972998106182504853332445631295887722169851026644987150881802490639715⟩ := by
  decide +kernel

theorem box_23_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 23 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      4334371858152926243081472965866035210135980313805396951504459422286231063195305606463702725299735⟩ := by
  decide +kernel

theorem box_23_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 23 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      833559388408152056593391249414803031056⟩ := by
  decide +kernel

theorem box_23_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 23 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      176885892450933370344648541722929792517336982848300444131156921386235110214094401358353806922059739383474451919921131510346892010793745346807666009284365⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
