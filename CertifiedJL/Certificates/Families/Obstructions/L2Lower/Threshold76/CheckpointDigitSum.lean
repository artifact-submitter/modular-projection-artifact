/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointData9

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution

theorem packedState9Checkpoint_digitSum :
    packedDigitSum cutoff packingBase packedState9Checkpoint = 9387937369855426309 := by
  set_option maxRecDepth 100000 in
  decide +kernel

end CertifiedJL.ThresholdLower76
