/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      808784848505222296107625153327388939956233878801369646034631417934569125220458124173611235909778390088377653920334490253357⟩ := by
  decide +kernel

theorem box_07_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      283469953866638877832350410952890308495269886678422977337654884741236145673187930350488844480920094244414884115893662281680012225491206⟩ := by
  decide +kernel

theorem box_07_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      110681287867419169456567859035109785902800138737860333908896190385069782311286170069437902050019492201499266788081271897654899245909020761678835509366836⟩ := by
  decide +kernel

theorem box_07_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      1076746819589988122847805993750358187505170863969663652836371184421520503176711175060479754620983676521261802410232512129805605740661513992555114223716⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
