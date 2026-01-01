/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint4_06_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint4Unit14_check :
    endpointUnitPassFromPaths128 (4 / 5) endpointPaths_4_div_5 14 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint4Unit15_check :
    endpointUnitPassFromPaths128 (4 / 5) endpointPaths_4_div_5 15 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
