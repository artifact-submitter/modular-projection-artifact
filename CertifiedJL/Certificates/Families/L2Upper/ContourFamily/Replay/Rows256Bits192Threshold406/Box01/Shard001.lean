/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      1243780336636552657115051325797039294153413967736690053560182218412255368812747470811796421132167862037728004172808327⟩ := by
  decide +kernel

theorem box_01_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      2367786111124291408323560010227404141619550347241651851243275939059361729102256296225809986448006462⟩ := by
  decide +kernel

theorem box_01_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      1169943335864221282993707543256141058687864103642078058905451765014742815485432938255359⟩ := by
  decide +kernel

theorem box_01_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      113640559010400190716476309049978080596869406447862924447745631614419882258237877091581571094530138102743151157972940533756260392740789957182531815046126⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
