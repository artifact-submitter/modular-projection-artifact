/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 14.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_14_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 14 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      728499639174832028423993891265312838168638714328849598189662876603698579108188362192613165040953133285253375225428201843438431389877751490352431254139076⟩ := by
  decide +kernel

theorem box_14_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 14 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1004148100936831233457944488922593322685267372530292030599916563778845501530346164059674375349169⟩ := by
  decide +kernel

theorem box_14_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 14 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      23223375505594461125298067621616362780⟩ := by
  decide +kernel

theorem box_14_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 14 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      76568138774259140587931046153134185866142287316898929435116812102862902970709611652400450666032980504342857780880866646803475401876949500626059662029898⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
