/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint9_01_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint9Unit04_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 4 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint9Unit05_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 5 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
