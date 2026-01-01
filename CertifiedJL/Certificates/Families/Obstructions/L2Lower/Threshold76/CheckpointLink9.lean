/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointLink8
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointStage9

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState9_eq_checkpoint : packedState 9 = packedState9Checkpoint := by
  calc
    packedState 9 = packedSquareStep cutoff packingBase scale (packedState 8) := by rfl
    _ = packedSquareStep cutoff packingBase scale packedState8Checkpoint := by
      rw [packedState8_eq_checkpoint]
    _ = packedState9Checkpoint := packedState8_to_checkpoint9

end CertifiedJL.ThresholdLower76
