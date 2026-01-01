/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointStage3
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointStage4

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState4_eq_checkpoint : packedState 4 = packedState4Checkpoint := by
  calc
    packedState 4 = packedSquareStep cutoff packingBase scale (packedState 3) := by rfl
    _ = packedSquareStep cutoff packingBase scale packedState3Checkpoint := by
      rw [packedState3_eq_checkpoint]
    _ = packedState4Checkpoint := packedState3_to_checkpoint4

end CertifiedJL.ThresholdLower76
