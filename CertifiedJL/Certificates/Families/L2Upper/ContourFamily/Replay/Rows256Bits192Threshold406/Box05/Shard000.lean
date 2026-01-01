/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      381975570597751297315520301974458594848813079903552811870672988617779781116582679267826498068673165311167210160572411240727861106623538145451708371551497⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      14782745371275268731777491836771254334549963857881793810678989148531231323162599025529244600945405204565166681184651879147530527230422509181650468286⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      6070419750279300104240089916894775502479477787323175947958584005616405597390793776851243606259242149943710191476720220313482846134082561100⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 5 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      78697194514405045899803983207509653143752312137987895905160896775823350645017582745737311189413525684844330716207796606263473719⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
