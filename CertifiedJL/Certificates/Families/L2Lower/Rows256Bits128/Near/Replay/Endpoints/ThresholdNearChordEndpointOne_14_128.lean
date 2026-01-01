/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_13_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit28_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 28 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit29_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 29 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
