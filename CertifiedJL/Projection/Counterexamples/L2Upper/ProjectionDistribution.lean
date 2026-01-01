/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow

/-!
# Compatibility exports for the sparse upper counterexample

The exact all-ones row distribution is owned by the neutral probability module
`CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow`. These exports preserve the
historical internal names used by the sparse upper-counterexample proof.
-/

namespace CertifiedJL.Counterexamples.SparseUpper.Internal

export Probability.SparseAllOnes
  (sparseRowSeedEquivBits sparseRowTrueCount sparseAllOnesRowSum
    sparseAllOnesRowSum_eq_trueCount sparseRowTrueCountFiberEquiv
    card_sparseRowTrueCount_fiber sparseAllOnesRowPMF
    sparseAllOnesRowPMF_apply_nat sparseAllOnesRowPMF_apply_int)

end CertifiedJL.Counterexamples.SparseUpper.Internal
