/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint19_17_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpointOneUnit00_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 0 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpointOneUnit01_check :
    endpointUnitPassFromPaths128 (1) endpointPaths_one 1 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
