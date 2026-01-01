/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 27.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_27_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 27 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      586384536231470323924154375741467020909070913654665450748951625403619911582314691194319927316706794015089058165543675935798520224188294422594760683755789⟩ := by
  decide +kernel

theorem box_27_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 27 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      2888407048774051783698525753822645523108897942948250495182681134924885657093625209480739539380288⟩ := by
  decide +kernel

theorem box_27_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 27 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      121144002442593687490747910906552852408214⟩ := by
  decide +kernel

theorem box_27_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 27 default)
      ⟨3, 0, 4⟩ =
      ⟨0,
      218619186858249774712360323173409487307863233292002230746771283925500789093359359673855912511017997674470365537730653817873194751392330654142918668389358⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
