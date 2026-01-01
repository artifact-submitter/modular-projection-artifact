/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint17_01_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint17Unit04_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 4 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint17Unit05_check :
    endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20 5 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
