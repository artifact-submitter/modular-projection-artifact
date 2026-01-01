/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      800081999787901656351890698153331608410691872830602456569242986606771965998751⟩ := by
  decide +kernel

theorem box_06_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      928029127781697566885771095293860972372809620665771986690981232544⟩ := by
  decide +kernel

theorem box_06_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      55131492658491886883869590179423786081930105361101947791155995029215756690470511644984532590344175908419347315851167979923165933678877308925453383960278⟩ := by
  decide +kernel

theorem box_06_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      2071543975008213984205867246973484805177732177250017032642435445211458464451267290014626393602951688845941369257027458414916088508600881730469189925536⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
