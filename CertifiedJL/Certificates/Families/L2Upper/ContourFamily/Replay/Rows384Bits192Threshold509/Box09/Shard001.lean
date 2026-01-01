/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      68174850248233110698759438165221566794993002225735626415558835771156786725324279422934341901926264708302989657116071055277946786⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      37241125283331180462646190573160354822353212552160768613232681428712005130766537669958197542201068278045538523807348537⟩ := by
  decide +kernel

theorem box_09_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      43143493287704477819282491861510321730971055992396137810281153052026769985126694682393955608093675873302744000⟩ := by
  decide +kernel

theorem box_09_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 9 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      689942636435839599424347834994635736424963331013154214619642642926842560116378201029823041669⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
