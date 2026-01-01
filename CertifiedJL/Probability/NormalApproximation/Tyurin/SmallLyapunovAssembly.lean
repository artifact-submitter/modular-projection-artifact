/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.SmallLyapunovOuter

/-!
# Assembly of Tyurin's small-Lyapunov estimate

This module recombines the core, outer, and Gaussian budgets proved in
`TyurinSmallLyapunovCore` and `TyurinSmallLyapunovOuter`.  It exports the
single scalar estimate consumed by the Prawitz-to-Berry--Esseen bridge.
-/

open MeasureTheory Set

noncomputable section

namespace CertifiedJL
namespace Probability

/--
The direct all-the-way-to-zero estimate for the weighted closed-budget
Prawitz functional.  Its three normalized contributions are bounded by
`19/200`, `11/500`, and `409/1000`, respectively.
-/
theorem tyurinSmallRationalDStar_lt_three_fifths
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    tyurinSmallRationalDStar L
        (tyurinSmallBranchCutoff L) (tyurinSmallBandwidth L) <
      3 / 5 := by
  have hcore := tyurinSmall_core_normalized_lt hL hsmall
  have houter := tyurinSmall_outer_normalized_lt hL hsmall
  have hgaussian := tyurinSmall_gaussian_normalized_lt hL hsmall
  unfold tyurinSmallRationalDStar
  rw [show
      (2 * (∫ u : ℝ in 0..tyurinSmallBranchCutoff L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) +
          2 * (∫ u : ℝ in
            tyurinSmallBranchCutoff L..tyurinSmallBandwidth L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u) +
          prawitzGaussianWeightedClosedBudget
            (tyurinSmallBranchCutoff L) (tyurinSmallBandwidth L)) / L =
        (2 * (∫ u : ℝ in 0..tyurinSmallBranchCutoff L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))) / L +
        (2 * (∫ u : ℝ in
            tyurinSmallBranchCutoff L..tyurinSmallBandwidth L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u)) / L +
        prawitzGaussianWeightedClosedBudget
          (tyurinSmallBranchCutoff L) (tyurinSmallBandwidth L) / L by ring]
  nlinarith

/--
For `0 < L ≤ 1/50`, the canonical rationalized Prawitz functional is
strictly below `3/5` at the small-Lyapunov cutoff and bandwidth.
-/
theorem tyurinRationalDStar_lt_three_fifths_of_small
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    tyurinRationalDStar L
        (tyurinSmallBranchCutoff L) (tyurinSmallBandwidth L) <
      3 / 5 := by
  exact (tyurinRationalDStar_le_small hL
    (one_le_tyurinSmallBandwidth hL hsmall)).trans_lt
      (tyurinSmallRationalDStar_lt_three_fifths hL hsmall)

end Probability
end CertifiedJL
