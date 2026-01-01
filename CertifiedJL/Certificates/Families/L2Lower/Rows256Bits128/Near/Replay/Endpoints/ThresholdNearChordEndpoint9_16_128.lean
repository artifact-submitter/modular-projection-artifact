/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint9_15_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint9Unit32_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 32 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint9Unit33_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 33 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
