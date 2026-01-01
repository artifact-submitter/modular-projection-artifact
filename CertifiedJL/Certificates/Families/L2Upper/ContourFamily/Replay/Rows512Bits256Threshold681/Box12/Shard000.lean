/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 12.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_12_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 12 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      738824295998519672277332813567241581657332441478713463745398019676110241786028711821025946220971421741275257655478577481243276211177227122436726313753362⟩ := by
  decide +kernel

theorem box_12_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 12 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      971279204191649213893352144942831706361854054076688374995770308019999403549421858993315031569152⟩ := by
  decide +kernel

theorem box_12_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 12 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      16730323889873786746739741339553142834⟩ := by
  decide +kernel

theorem box_12_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 12 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      77772861131890535010273076643152676532459171766319464067265277070183724261852151336032693990766420903949986478686636314865856184017866530652272023810500⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
