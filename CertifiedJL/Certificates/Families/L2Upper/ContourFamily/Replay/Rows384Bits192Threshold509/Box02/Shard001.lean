/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      59555483400108103656242986549676655513600803220349237036709544094034824374584655284721008561253363483597776251199096518011219012⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      31671217166004587849478187999488339632198447553934332434345098486651409535090099093546113099873852208132232247178858422⟩ := by
  decide +kernel

theorem box_02_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      35274827319538056383857667610086840522467722848520467302651053473599857770977290220012498444197113405786452746⟩ := by
  decide +kernel

theorem box_02_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      454164422981401581780742372372696549225578748800990532580116776277493482108396824674432911869⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
