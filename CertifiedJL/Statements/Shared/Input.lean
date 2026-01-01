/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Model.Vectors.SquaredNorm
import CertifiedJL.Statements.Shared.ExactRatio

/-!
# Protocol-facing input conditions

Cap-relative projection theorems constrain the actual input norm. Protocol
soundness instead starts from a public threshold known to be no larger than
the input norm. These exact predicates keep those two interfaces distinct.
-/

namespace CertifiedJL

/-- Every coefficient is the centered representative of its residue class
modulo `q`. This prevents a theorem about integer representatives from being
applied to an arbitrary congruent lift. -/
def CenteredInput (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Prop :=
  ∀ i, w i ∈ centeredInterval q

/-- The public natural threshold is no larger than the Euclidean norm of `w`,
expressed without square roots. -/
def InputThresholdAtMostNorm (inputThreshold : ℕ) {d : ℕ}
    (w : Fin d → ℤ) : Prop :=
  inputThreshold ^ 2 ≤ sqNorm w

/-- Exact modulus margin `margin * inputThreshold ≤ q`. -/
def InputThresholdWithinModulus
    (margin : NonnegativeRatio) (q inputThreshold : ℕ) : Prop :=
  margin.numerator * inputThreshold ≤ margin.denominator * q

end CertifiedJL
