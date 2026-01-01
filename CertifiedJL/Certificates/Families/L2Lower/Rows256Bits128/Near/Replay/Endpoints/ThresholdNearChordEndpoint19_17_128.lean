/- Copyright (c) 2026 Anonymous Author. All rights reserved. -/
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpoint19_16_128

namespace CertifiedJL.ThresholdNearChord128

theorem endpoint19Unit34_check :
    endpointUnitPassFromPaths128 (19 / 20) endpointPaths_19_div_20 34 = true := by
  set_option maxRecDepth 100000 in decide +kernel

end CertifiedJL.ThresholdNearChord128
