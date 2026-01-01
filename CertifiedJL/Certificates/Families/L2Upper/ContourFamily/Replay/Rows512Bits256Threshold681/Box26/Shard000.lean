/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 26.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_26_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 26 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      628231194181475464603701687212500823320813308276337296410698085286147893011347632720941011456641150081450628942854034361561878679790347928923151469520357⟩ := by
  decide +kernel

theorem box_26_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 26 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      2391735260728834560155494636525173671991925382576531106395853688197492697247840506760351011575029⟩ := by
  decide +kernel

theorem box_26_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 26 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      8791479163198634417253452078983495928212⟩ := by
  decide +kernel

theorem box_26_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 26 default)
      ⟨3, 0, 4⟩ =
      ⟨0,
      102577933964247743653580552593988682685104971225716875062254454267783326510434564936390827844303071643077661537380866383472728874382651589698586125769052⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
