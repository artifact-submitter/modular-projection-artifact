/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 11.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_11_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      498846560169415368901924229690469112002821818967103085929989250704075586073546541757941014245643359388215472066686621089802513166507102170718158113792303⟩ := by
  decide +kernel

theorem box_11_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1580060077487221166097395232002988274216837317243565455767430320952310390262593306251953847633073188150081703195055366883548684301588500963388871568816⟩ := by
  decide +kernel

theorem box_11_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4292248751153587121873758379087082264791492395316057453520501867973680652724703736620119901948895699391421515358782173539088054927256192454947915⟩ := by
  decide +kernel

theorem box_11_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      72590448298034232943086042244990153433235503218988946486327208763836523853523998853216153497610523524356351583290569370133481281203860565⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
