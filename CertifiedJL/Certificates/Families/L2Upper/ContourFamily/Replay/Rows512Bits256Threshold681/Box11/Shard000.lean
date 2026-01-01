/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 11.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_11_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 11 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      742313176660453258961091346724711832575263271441055518750899070041232654713245551073021826399560324115382445581832937757243217449733172279881743361240055⟩ := by
  decide +kernel

theorem box_11_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 11 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      963426356924342242271281548676954687854070136659409008636161674793371003974838414412655865868346⟩ := by
  decide +kernel

theorem box_11_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 11 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      15474007421085518089322047124970121104⟩ := by
  decide +kernel

theorem box_11_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 11 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      78179371773890930581158195316682598530744492109387910516352447819293588098521535237136978451921709199756882185470276336093026560754244576140197324319112⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
