/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint19_14_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint19Unit30_check :
    endpointUnitPassFromPaths128 (19 / 20) endpointPaths_19_div_20 30 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint19Unit31_check :
    endpointUnitPassFromPaths128 (19 / 20) endpointPaths_19_div_20 31 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
