/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_10_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit22_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 22 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit23_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 23 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
