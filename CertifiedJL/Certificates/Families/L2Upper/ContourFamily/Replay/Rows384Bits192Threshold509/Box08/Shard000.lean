/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      611101772293595683202613893637183795567518436409723075549544240142800681577792173249130324148672991816146453912636208315294545289219956582636183927761194⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1813035709381703204085350775078340569371808255576066351291327406442593276255299060148619957744939483008879329830255022532460805220744160283402407591163⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4182657366193001430026496043484932403328963089322086618153943495494637068895487297666080196686897200764846902994358663094053837985291919490925955⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      59074852243976988031389823874889567220624382051191470869401102305689705673246080713835612463863880269229376393314418298963728145796573087⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
