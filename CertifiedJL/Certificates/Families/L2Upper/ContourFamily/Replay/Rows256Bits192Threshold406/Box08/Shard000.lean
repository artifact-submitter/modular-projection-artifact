/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      88975433760334117688306824138844632629274994784449092565109575810187991502315958746701426146365510976763687652786102058940979397759543446931271936625616⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      681542081099776997061973247258050458569746703280917382335409906794951270719124144114828338874246197196905312729315549353554478711925590969902392405946⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      12946726735630397348154393504500821479279014092227284918680162110345907284945134490151487850729715976953217268808975842134454275496829362944489⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 8 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      13069234298177614994051156289056039190969988516484352753694574363475607297278657712015627613926762638693218440839905665520480553050871⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
