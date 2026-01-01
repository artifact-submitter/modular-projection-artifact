/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointLink6
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointStage7

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState7_eq_checkpoint : packedState 7 = packedState7Checkpoint := by
  calc
    packedState 7 = packedSquareStep cutoff packingBase scale (packedState 6) := by rfl
    _ = packedSquareStep cutoff packingBase scale packedState6Checkpoint := by
      rw [packedState6_eq_checkpoint]
    _ = packedState7Checkpoint := packedState6_to_checkpoint7

end CertifiedJL.ThresholdLower76
