/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_09_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit20_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 20 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit21_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 21 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
