/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.DirectProvider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.FourierProvider128

/-! # Complete dominant public-threshold provider at 128 bits -/

open scoped ENNReal

namespace CertifiedJL

/-- The complete margin-three dominant high-activity provider at 128 bits. -/
theorem sparseThresholdDominantHighActivity128_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128) :
    SparseThresholdDominantHighActivity128BoundAt
      (NonnegativeRatio.ofNat 3) := by
  intro q d w inputThreshold i hq hcentered hpositive hnorm hmodulus
    hdominant hmax
  have hi : w i ≠ 0 := by
    intro hiZero
    rw [hiZero] at hdominant
    simp at hdominant
  have hmargin : 3 * inputThreshold ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmodulus
  by_cases huHalf : dominantResidualRatio w i ≤ 1 / 2
  · exact sparseThresholdDominantHighActivity128_lowResidual_of_replay replay
      w inputThreshold i hq hcentered hpositive hnorm hmargin hdominant huHalf
  · exact sparseThresholdDominantHighActivity128_fourierHighResidual_of_replay replay
      w inputThreshold i hq hcentered hpositive hi hdominant hmax
        (le_of_not_ge huHalf) hmargin

end CertifiedJL
