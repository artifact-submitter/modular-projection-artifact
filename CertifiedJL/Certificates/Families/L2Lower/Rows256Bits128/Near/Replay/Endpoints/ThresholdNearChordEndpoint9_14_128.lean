/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint9_13_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint9Unit28_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 28 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint9Unit29_check :
    endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10 29 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
