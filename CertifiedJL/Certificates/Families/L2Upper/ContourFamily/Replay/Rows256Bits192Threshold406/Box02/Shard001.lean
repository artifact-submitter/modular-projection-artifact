/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      1356653447603160982442523719323229903297016834593600324632771165333770870925607224046571822464055172050213223306688692⟩ := by
  decide +kernel

theorem box_02_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      3834290755775972188308838411403147156269124326915572777455181470060427358695146474979488076676422160⟩ := by
  decide +kernel

theorem box_02_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      6896609340495546332967478169850525807323754847066558105022030849448887167731926744329063292912010514112733691⟩ := by
  decide +kernel

theorem box_02_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      86457781985055215994065386791004066203201850355067225863820213633662131315020362500850876521564913132050145558888717108956492038044991120212432670925526⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
