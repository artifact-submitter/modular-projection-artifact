/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      10831223403061529149542932979488197235849256421101723356283425196062020387061927876319746899563891462210779119895125304919289⟩ := by
  decide +kernel

theorem box_03_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      734207717458291477888399166970154862239952956658607091536549977636755267498440224931694095479941758856753594⟩ := by
  decide +kernel

theorem box_03_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      347539714077693826682587935102542685406070204720903744962157794909109270005347405957094783200557367100630744822⟩ := by
  decide +kernel

theorem box_03_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 3 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      118049051340259048368144828239151424650456338478971632323703812706702894397584789063537425578606595314387731600553453757087925303183402269890881799910412⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
