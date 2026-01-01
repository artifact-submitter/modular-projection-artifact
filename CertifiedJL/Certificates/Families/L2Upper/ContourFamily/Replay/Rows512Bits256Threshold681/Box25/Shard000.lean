/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 25.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_25_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 25 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      650698247970180683776293424525350241275781362137926207654568610684167548946061176316440549028212793429261031370579938410199036739203323926087781519172074⟩ := by
  decide +kernel

theorem box_25_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 25 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      2007333402893153879779802292717118935801644700680614035346181666213801094980234440104816443388060⟩ := by
  decide +kernel

theorem box_25_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 25 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      1015592893191956468957069713073649109493⟩ := by
  decide +kernel

theorem box_25_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 25 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      77381883533899465747468323804638940293911979610265430087140044977138707873597540985492124290489396537368002021119397337037691556869607891146923608569854⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
