/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      10313291432321426044101277147892676817115922809678204479415025425910018483011008936512454806855964014281948774728807971263111⟩ := by
  decide +kernel

theorem box_02_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      558220999878485091283184928465829398071040127581712995370335381092731034549070719741481613089520778802339307⟩ := by
  decide +kernel

theorem box_02_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      1218324312853258557447896787955569664407936961613033697617594671149570653694916190955894915791699⟩ := by
  decide +kernel

theorem box_02_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      117452969508119116497402275278654107108869778679950289521398747951496652552350116378136728261083088656754354582431757870010023651163288854378124704791686⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
