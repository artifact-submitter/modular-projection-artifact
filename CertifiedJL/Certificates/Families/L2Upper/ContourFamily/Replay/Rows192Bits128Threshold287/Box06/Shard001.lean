/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      4446593451275858179300679727066970586846529643275113203359119669067481326015231054931241621055340182396013411212464244321131637445959521870⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      56283958932100673574621363189039603418406170270786309361437759137257462637045638151662513691947786772704852971988209740929022548628311⟩ := by
  decide +kernel

theorem box_06_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      2140905733276181848289244971875237961623371109485820822092082704421840202816900599998984397817215325627409838939512493233729411848⟩ := by
  decide +kernel

theorem box_06_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      168814020071484774702969255872438599380440317212589076404527664440294471830594371744354418079043294080809044905111851761807⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
