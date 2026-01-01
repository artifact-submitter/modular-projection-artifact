/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 15.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_15_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      87855876439917914023763543253082028397385845309536130924897087946096832792818553105683197478017029478591277998922238830080466980896623825545928823168390⟩ := by
  decide +kernel

theorem box_15_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      2345162250222243829819991985551841812234295545245470188314198352515224715739878944861253498427042498962104258944348405050882696772156346140669532206927⟩ := by
  decide +kernel

theorem box_15_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      56905703904661842584533905015905265975330297636452808929220097625432328488089275430167018247723152049774625177049764933559143509934922641760051015⟩ := by
  decide +kernel

theorem box_15_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 15 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      8134638939364739427688658240328002042043827828711083028873264461225668545765183019479704516459582252953050873884037558441536954367997413095⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
