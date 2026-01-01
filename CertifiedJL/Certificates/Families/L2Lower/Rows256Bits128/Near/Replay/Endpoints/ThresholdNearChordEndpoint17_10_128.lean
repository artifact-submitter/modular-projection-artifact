/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint17_09_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint17Unit20_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 20 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint17Unit21_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 21 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
