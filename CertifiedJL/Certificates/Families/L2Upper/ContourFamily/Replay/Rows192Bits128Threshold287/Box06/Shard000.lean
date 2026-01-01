/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      523540202898983169913080309373013450894100988096224012354258869646038697743807028963083812463503371884025744035838163310319093070781651506076532121725161⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      14831020265864512880320293286450301241113939229907162519771706721803019177561577397609725163755000856000294705948538985049275955551809023295088356624650⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      9620860874831428043466310062445273002540299368850033376168888622836082548036212803742516780085142502992620774006629316764829635038435694512324741806⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 6 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      377362301577162505727700231221787767796684625625301924211208475648399017303223077873138121721496421246539519355812270639671160708440780456550587⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
