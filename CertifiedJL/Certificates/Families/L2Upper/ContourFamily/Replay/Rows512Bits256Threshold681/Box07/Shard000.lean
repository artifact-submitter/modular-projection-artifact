/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 7 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      767161463912670343717569066419462634609286004468463191914090356122065067520506033227262612364123121586772434174116744086883487179549682148661450317623747⟩ := by
  decide +kernel

theorem box_07_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 7 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1456726927950501628329066059270401039099878863129159992620033544616830266354134690110747989430123⟩ := by
  decide +kernel

theorem box_07_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 7 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      20564385546937233943993459228347845074⟩ := by
  decide +kernel

theorem box_07_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 7 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      155884587000853334559519458286407567453623852782765109759090170527834109589911353065376275330804600224300499353058813468784701129340695043566439849904038⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
