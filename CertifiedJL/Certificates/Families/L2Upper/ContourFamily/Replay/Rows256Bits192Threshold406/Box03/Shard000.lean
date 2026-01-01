/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      512580810335930351297017476673473278439552597928795719190389461670407960218578560171516624230942179932857816558337955543992211616586125550611247611663647⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      12869395210021611722736147033290362607134904428470447687026405277795637067810137159150415808744866334405408295005034365533646145544160723126489994058⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3358500314303045818831798302237704438557888146074307799536647341788796988710648483897022507838613975085179022050257580340680156689225660950⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      31638003645856590176178086480150997956200767438422111525613890187083046567141952260324177423338613994705733490504657265849570693⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
