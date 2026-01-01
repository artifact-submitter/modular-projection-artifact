/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Finite.LocalSoundness
import CertifiedJL.Certificates.Families.OneRow975.Finite.NatVerified

/-!
# Global soundness of the sparse one-row scalar certificate

The analytic cell bounds live in `LocalSoundness.lean`, which deliberately
does not import any generated certificate data.  The production certificate
is the nonnegative `NatInterval` evaluator in `NatVerified.lean`; this small
module is the compatibility bridge from its all-cell theorem to the public
real-valued API.
-/

namespace CertifiedJL
namespace SparseOneRowCertificate

/-- Every committed scalar cell has a proved strict Nat-interval check. -/
theorem cellCheck_verified {index : ℕ} (hindex : index < gridSize) :
    natCellCheck index = true :=
  NatInterval.natCellCheck_verified hindex

/-- The verified scalar envelope is strictly below `2⁻¹⁴²` on one cell. -/
theorem scalarEnvelope_lt_target
    {index : ℕ} {y : ℝ}
    (hcell :
      (cellLeftRat index : ℝ) ≤ y ∧
        y ≤ (cellRightRat index : ℝ))
    (hindex : index < gridSize) :
    scalarEnvelope y < (target : ℝ) :=
  NatInterval.natScalarEnvelope_lt_target hcell hindex

/-- Soundness of the retained scalar certificate on its exact profile range. -/
theorem scalarEnvelope_lt_target_of_le_certifiedProfileUpper
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ (certifiedProfileUpper : ℝ)) :
    scalarEnvelope y < (target : ℝ) := by
  obtain ⟨index, hindex, hcell⟩ :=
    exists_certificate_cell_of_le_certifiedProfileUpper hy0 hy
  exact scalarEnvelope_lt_target hcell hindex

end SparseOneRowCertificate
end CertifiedJL
