/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint17_14_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint17Unit30_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 30 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint17Unit31_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 31 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
