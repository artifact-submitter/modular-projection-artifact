/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Spec
import CertifiedJL.Projection.OneRow.BalancedTernary.ProfileSplit

/-! # Profile-split assembly for the balanced-ternary one-row result -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CertifiedJL

open Probability

namespace CertificateAssembly

/-- The two bounded certificate claims feed the exact normalized theorem. -/
theorem normalizedRademacher975Upper
    (moderate : CertificateContracts.ModerateGrid)
    (envelope : CertificateContracts.SparseOneRowEnvelope) :
    NormalizedRademacher975UpperStatement := by
  exact normalizedRademacher975Upper_of_profileSplit moderate envelope

/-- Shared sparse one-row assembly below the reader-facing syntax wrapper. -/
theorem sparseOneRow975
    (moderate : CertificateContracts.ModerateGrid)
    (envelope : CertificateContracts.SparseOneRowEnvelope) :
    SparseOneRow975Statement :=
  sparseOneRow975_of_normalizedRademacherUpper
    (normalizedRademacher975Upper moderate envelope)

end CertificateAssembly
end CertifiedJL
