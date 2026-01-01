/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint9_04_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint9Unit10_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 10 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint9Unit11_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 11 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
