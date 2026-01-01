/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_05_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit12_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 12 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit13_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 13 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
