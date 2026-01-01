/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Finite.Soundness
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs
import CertifiedJL.Projection.OneRow.BalancedTernary.ProfileSplit

/-!
# Sparse one-row theorem assembly

This internal module combines the bounded 24-cell tilted-Rademacher replay,
the 308-cell scalar-envelope prefix, and the elementary endpoint branches.
The reader-facing theorem is in
`CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform`.
-/

namespace CertifiedJL

/-- The normalized Rademacher form of the strict one-sided `2⁻¹⁴²` bound. -/
theorem normalizedRademacher975Upper :
    NormalizedRademacher975UpperStatement := by
  apply normalizedRademacher975Upper_of_profileSplit
  · exact TyurinModerate.moderateGridCells_certified
  · intro y hy0 hy
    exact SparseOneRowCertificate.scalarEnvelope_lt_target_of_le_certifiedProfileUpper
      hy0 (by simpa [SparseOneRowProfileSplit.largeProfileCutoff] using hy)

/-- Internal assembly of the sparse one-row statement contract. -/
theorem sparseOneRow975_assembly : SparseOneRow975Statement :=
  sparseOneRow975_of_normalizedRademacherUpper
    normalizedRademacher975Upper

end CertifiedJL
