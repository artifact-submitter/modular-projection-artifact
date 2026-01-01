/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint19_11_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint19Unit24_check :
    endpointUnitPassFromPaths128 (19 / 20) endpointPaths_19_div_20 24 = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem endpoint19Unit25_check :
    endpointUnitPassFromPaths128 (19 / 20) endpointPaths_19_div_20 25 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
