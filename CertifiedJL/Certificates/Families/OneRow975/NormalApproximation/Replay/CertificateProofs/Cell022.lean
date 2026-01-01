/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.OuterPlan
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Data.Grid

namespace CertifiedJL
namespace TyurinModerate
namespace CertificateProofs
namespace Cell022

set_option maxRecDepth 10000

/-- The moderate-grid cell at index 22 replayed by this shard. -/
def certificateCell : Cell :=
  moderateGridCells[22]'(by decide)

/-- The 53-cell scaled outer plan is locally safe. -/
theorem outerPlan : outerPlanCheck certificateCell = true := by
  decide +kernel

/-- The generated scaled-coordinate certificate semantically certifies this grid cell. -/
theorem cellCertified : CellCertified certificateCell := by
  apply cellCertified_of_crossingCore_outerPlan
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact outerPlan
  · decide +kernel

end Cell022
end CertificateProofs
end TyurinModerate
end CertifiedJL
