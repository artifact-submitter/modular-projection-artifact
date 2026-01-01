/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      1095801363078504223741545057159524919205183517785020703187617405510101745173430834046830302219912783782861763104⟩ := by
  decide +kernel

theorem box_02_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      1985657130546236527803131171361920447488854091010514544510976282905003079786787924260494656723532258438944594386480⟩ := by
  decide +kernel

theorem box_02_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      134612129713716675004021844863600643550589248483362028662024146531761235686668926346279879312035473680985401272281346087182893221904509058236937573200363⟩ := by
  decide +kernel

theorem box_02_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      353105887680845215294093326184606373509251400155461964643294558480634107720787457805900295489337992746965520990940452473353928443746880277942907084831⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
