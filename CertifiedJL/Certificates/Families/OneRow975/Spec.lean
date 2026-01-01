/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Finite.LocalSoundness
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Assembly

/-!
# Semantic certificate contracts for the one-row results

These propositions are the exact boundaries between finite certificate replay
and the shared analytic assembly.  Neither proposition is a probability
theorem.
-/

namespace CertifiedJL.CertificateContracts

/-- The retained 24-cell tilted-normal grid on `L ∈ [1/50, 0.19707]`. -/
def ModerateGrid : Prop :=
  ∀ C ∈ TyurinModerate.moderateGridCells,
    TyurinModerate.CellCertified C

/-- The retained scalar-envelope prefix on `B ∈ [0,32/125]`. -/
def SparseOneRowEnvelope : Prop :=
  ∀ y : ℝ, 0 ≤ y →
    y ≤ (SparseOneRowCertificate.certifiedProfileUpper : ℝ) →
    SparseOneRowCertificate.scalarEnvelope y <
      (SparseOneRowCertificate.target : ℝ)

end CertifiedJL.CertificateContracts
