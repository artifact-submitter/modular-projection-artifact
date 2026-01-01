/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      581118720907352828894683233507970811193559314049689534445868736270417787962788328297849363815223118310051206486594593220480098060757898009528400964835504⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1762798519253344854480304064143637012338396791462110499726402181873688311151986152978133601271822575468536360447692220461048524168135762405141360791577⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4235678048921210475317192743828195947115990439340027143977646073283094767073611730569069226968673055485976792174659539592218108458420526230927487⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      62031628964110539997205418859690570758133729036196729724818356553119760471482727155094410508298133775314852151202890129337994806827624639⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
