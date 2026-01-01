/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_06_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit14_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 14 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit15_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 15 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
