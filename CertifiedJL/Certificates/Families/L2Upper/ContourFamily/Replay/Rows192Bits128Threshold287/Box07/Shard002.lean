/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      20001924177722650790417329370804015779230141366688204297772790650726827937776740394022221164363435425118741657391439667094443078118810⟩ := by
  decide +kernel

theorem box_07_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      134140924061323397323889106049611886207185546496666894150533029898762316102711866824491585430221083251431325347152004376380925419539494464618679089212350⟩ := by
  decide +kernel

theorem box_07_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      2041726530227273853237442004236252334815870849708644096615781158875520585363633697260445274417843915844870968758903982947843349291932728200428573121297⟩ := by
  decide +kernel

theorem box_07_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      167041611652894275418561247800826006146477438589218966292155466259708307979941173271970043659649481348692427283776814189455961269575543575417179⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
