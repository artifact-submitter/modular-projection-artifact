/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_04_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit10_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 10 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit11_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 11 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
