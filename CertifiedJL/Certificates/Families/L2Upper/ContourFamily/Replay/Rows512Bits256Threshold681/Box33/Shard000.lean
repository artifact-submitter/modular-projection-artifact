/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 33.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_33_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 33 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      56273872076684862896549080579494115264491832592544630101434463021111072335013002529758716869074844424525553812776957087770007718268640975005713119472986⟩ := by
  decide +kernel

theorem box_33_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 33 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      951236120012776250894383873906642770130061991196540776453789535366039564815896606411065578603193425269940536736618510⟩ := by
  decide +kernel

theorem box_33_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 33 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      32881515412616486471056353436516496267626344410724468799391923997305325613214891900064102125794615588769951185371321223170758354819079732067511516811494⟩ := by
  decide +kernel

theorem box_33_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 33 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      560856912237468811634251786234279011347753744569091282174589499795163500541260896412108936416493998675630518726774952930671177436949090351385106913985⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
