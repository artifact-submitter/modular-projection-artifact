/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      6912821417236658751172408822816497024075591648134868724636410239724864187683519073599676116739890799572124511140127288⟩ := by
  decide +kernel

theorem box_05_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      804494284787483223134955249571853528375739357202133169977700731498539180365607864460205651425026158026⟩ := by
  decide +kernel

theorem box_05_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      72396053171686517036975456808822851794741658758593649041650518563572729989105120251569884335784151202026501078452949311905539346289564418076372886116245⟩ := by
  decide +kernel

theorem box_05_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      20028716402434195439611404745725008267253234282559689729274645672830874241086490654377078939529794374164204449475699279113142827698822929662159711269056⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
