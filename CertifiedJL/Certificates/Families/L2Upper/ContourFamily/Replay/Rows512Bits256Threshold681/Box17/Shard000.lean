/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 17.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_17_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 17 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      712029419972898800700574206994724968381891339937264231435579607641718046251935398943657254077489729244300855644318684494409498666672976300487425112627537⟩ := by
  decide +kernel

theorem box_17_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 17 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1631262221522095023136388454454464926160495831020071596338929317654663504178857790681634941548777⟩ := by
  decide +kernel

theorem box_17_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 17 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      69740147933819452590737929710388684987⟩ := by
  decide +kernel

theorem box_17_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 17 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      340158146360551528012368609623894550940282943261440411221167668703599456045944388872184579955487162242512659150905060907671086913684286862301724772747877⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
