/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 21.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_21_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 21 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      693875607532040835593920191224413492538238993733223237375390868006487061695454650428112817965224423952545845579814170028465502906481775399950097821805803⟩ := by
  decide +kernel

theorem box_21_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 21 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      4095706592427208985092165594220281735810481354675090116211049342790970840429840805909882533997954⟩ := by
  decide +kernel

theorem box_21_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 21 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      442343851155681912424446136886805687434⟩ := by
  decide +kernel

theorem box_21_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 21 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      180464182539089634331870496902861971026448726481793735384109269898758346381128182312802186922120841010567286570541943843250979822819660441568257963296455⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
