/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointLink5
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointStage6

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState6_eq_checkpoint : packedState 6 = packedState6Checkpoint := by
  calc
    packedState 6 = packedSquareStep cutoff packingBase scale (packedState 5) := by rfl
    _ = packedSquareStep cutoff packingBase scale packedState5Checkpoint := by
      rw [packedState5_eq_checkpoint]
    _ = packedState6Checkpoint := packedState5_to_checkpoint6

end CertifiedJL.ThresholdLower76
