/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointLink4
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointStage5

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState5_eq_checkpoint : packedState 5 = packedState5Checkpoint := by
  calc
    packedState 5 = packedSquareStep cutoff packingBase scale (packedState 4) := by rfl
    _ = packedSquareStep cutoff packingBase scale packedState4Checkpoint := by
      rw [packedState4_eq_checkpoint]
    _ = packedState5Checkpoint := packedState4_to_checkpoint5

end CertifiedJL.ThresholdLower76
