/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointData6
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointData7

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState6_to_checkpoint7 :
    packedSquareStep cutoff packingBase scale packedState6Checkpoint =
      packedState7Checkpoint := by
  set_option maxRecDepth 100000 in
  decide +kernel

end CertifiedJL.ThresholdLower76
