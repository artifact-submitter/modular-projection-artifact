/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint17_17_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint17Unit36_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 36 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint17Unit37_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 37 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
