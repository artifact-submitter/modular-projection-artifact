/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearChordEndpointPaths128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint4Unit00_check :
    endpointUnitPassFromPaths128 (4 / 5) endpointPaths_4_div_5 0 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint4Unit01_check :
    endpointUnitPassFromPaths128 (4 / 5) endpointPaths_4_div_5 1 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
