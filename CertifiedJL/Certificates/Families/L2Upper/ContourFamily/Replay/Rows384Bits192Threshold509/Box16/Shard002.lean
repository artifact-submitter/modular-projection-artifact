/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 16.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_16_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      10263093546752798738774651390425173205760311329376054150107139711138514781816745219631548403552144675686285436851622082624365804556522205943222778795341⟩ := by
  decide +kernel

theorem box_16_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      16770013710949171397851281568386404443440075720265647392912774969966747782361887553628635284893447195162913967351965328604788068468330974468638987315127⟩ := by
  decide +kernel

theorem box_16_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      97631424946031066608345614538811155513991000382325640114154083330764158432910452196283912051202001410370346386953503987079558212667567685344825628818⟩ := by
  decide +kernel

theorem box_16_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      1651010077974925261076362416651125850005930586296712806271544888522882310842873342623393974426651848751359946866282333105636784516094885973846⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
