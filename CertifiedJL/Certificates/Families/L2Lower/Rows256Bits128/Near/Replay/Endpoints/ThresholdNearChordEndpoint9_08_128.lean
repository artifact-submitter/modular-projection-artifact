/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint9_07_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint9Unit16_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 16 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint9Unit17_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 17 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
