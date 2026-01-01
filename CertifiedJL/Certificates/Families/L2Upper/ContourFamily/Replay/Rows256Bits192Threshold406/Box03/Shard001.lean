/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      1615817338211611315537679310995100542857435867342314888756664316146660964996121918177019290119216216692400521275669947⟩ := by
  decide +kernel

theorem box_03_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      7737350096278353261856187527941393651610704187327266655129573387076516969025794497800107659987933210⟩ := by
  decide +kernel

theorem box_03_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      467722727834341264432629035359819163682591792620721214536672966127875098148408223222875096009270252959004321872143252081298619173728016⟩ := by
  decide +kernel

theorem box_03_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 3 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      91795452429503097961755397271953299492670249363775774827436827886102218308830465357630266567875651868938845684236947764062758275454405399570345206740052⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
