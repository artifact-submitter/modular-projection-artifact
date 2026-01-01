/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint9_10_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint9Unit22_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 22 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint9Unit23_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 23 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
