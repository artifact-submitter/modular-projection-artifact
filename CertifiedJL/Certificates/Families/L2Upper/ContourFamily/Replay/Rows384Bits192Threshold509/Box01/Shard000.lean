/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      740784369650222965430070677686102333459427890634072463497688702350234514723181939176264216950531619833804621614804784128699207827513180744218490835245690⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      2086757669421589715549244400459586248937256020302659777021148615912473270576854638903776939887135627866226625658823362357592325992136550990094814916875⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4386022477786060454633320992246508988383917134223435014190741893850595958390166047539246317477103396343587258621976269915546233758535128242862671⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      57343507385388202659489902917570014691346787800297807001008896679782047333810069407374955322251662270280306635869224534982847535392050280⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
