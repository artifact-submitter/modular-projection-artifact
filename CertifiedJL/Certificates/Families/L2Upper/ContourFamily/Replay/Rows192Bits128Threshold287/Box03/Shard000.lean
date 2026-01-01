/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      698093334101537000142147156108796086558138328161147812159264653941502064182581809929168559669163727460493050914038400391721948424488658418150738929132456⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      13354603997090882772319870849549478072808324399494635948566599338382075970364034165050083940702537520725238929097218459943331239467714688006236388725578⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3916603841389703400318349770221262404441990286356638367139069651842015716681638193831516208911221549581097878992960407739059636785411376492088067455⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      75345207529438196704589383385247704249841843712769655154038304500901585508208558787543076464760018650457504283556046371429895464008754349889219⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
