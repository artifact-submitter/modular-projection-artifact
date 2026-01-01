/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      1185058167400801502514716883891389308672035237336824355358695522258136467808446121966305386844080940965937332653799332568⟩ := by
  decide +kernel

theorem box_06_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      6450958697730486806151999277985177083363117634378857465930575699356566817613499871788789832954217669266858805831⟩ := by
  decide +kernel

theorem box_06_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      148892622911144410798068803123034928972029674891879593275160666977842962734083755763396525124612697643859408979230563523786013145009337700270336038824094⟩ := by
  decide +kernel

theorem box_06_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      3670346994665895604880075858434726436611500639081857128570667052575181216427416004549881520389360978255106481956608066348979731375006054725959583564122⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
