/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointLink7
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointStage8

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState8_eq_checkpoint : packedState 8 = packedState8Checkpoint := by
  calc
    packedState 8 = packedSquareStep cutoff packingBase scale (packedState 7) := by rfl
    _ = packedSquareStep cutoff packingBase scale packedState7Checkpoint := by
      rw [packedState7_eq_checkpoint]
    _ = packedState8Checkpoint := packedState7_to_checkpoint8

end CertifiedJL.ThresholdLower76
