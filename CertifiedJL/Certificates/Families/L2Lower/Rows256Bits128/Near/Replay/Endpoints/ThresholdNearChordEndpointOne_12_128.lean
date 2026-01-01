/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_11_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit24_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 24 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit25_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 25 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
