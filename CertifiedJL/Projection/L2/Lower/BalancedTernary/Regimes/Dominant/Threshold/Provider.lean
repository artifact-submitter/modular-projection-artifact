/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.DirectProvider
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.FourierProvider

/-! # Target-neutral dominant public-threshold provider -/

namespace CertifiedJL

/-- Assemble the direct, Fourier, and retained dominant branches for an
arbitrary target configuration. -/
theorem sparseThresholdDominantHighActivity_of_replay_at
    (config : ThresholdTailConfig) {highBudget : ℝ}
    (replay : CertificateContracts.SparseL2ThresholdDominantReplayAt
      config.rows config.squaredNormFloor highBudget)
    (hbudget : 0 < highBudget)
    (hhighBudget : config.highBudget = ENNReal.ofReal highBudget) :
    SparseThresholdDominantHighActivityBoundAt config
      (NonnegativeRatio.ofNat 3) := by
  intro q d w inputThreshold i hq hcentered hpositive hnorm hmodulus
    hdominant hmax
  have hi : w i ≠ 0 := by
    intro hiZero
    rw [hiZero] at hdominant
    simp at hdominant
  have hmargin : 3 * inputThreshold ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmodulus
  rw [hhighBudget]
  by_cases huHalf : dominantResidualRatio w i ≤ 1 / 2
  · exact sparseThresholdDominantHighActivity_lowResidual_of_replay_at
      replay hbudget w inputThreshold i hq hcentered hpositive hnorm hmargin
        hdominant huHalf
  · exact sparseThresholdDominantHighActivity_fourierHighResidual_of_replay_at
      replay hbudget w inputThreshold i hq hcentered hpositive hi hdominant
        hmax (le_of_not_ge huHalf) hmargin

/-- Assemble the direct, tilted-Fourier, and retained dominant branches for
an arbitrary target configuration. -/
theorem sparseThresholdDominantHighActivity_of_tiltedReplay_at
    (config : ThresholdTailConfig) {singletonTilt cappedTilt highBudget : ℝ}
    (replay : CertificateContracts.SparseL2ThresholdDominantTiltedReplayAt
      config.rows config.squaredNormFloor singletonTilt cappedTilt highBudget)
    (hbudget : 0 < highBudget)
    (hhighBudget : config.highBudget = ENNReal.ofReal highBudget) :
    SparseThresholdDominantHighActivityBoundAt config
      (NonnegativeRatio.ofNat 3) := by
  intro q d w inputThreshold i hq hcentered hpositive hnorm hmodulus
    hdominant hmax
  have hi : w i ≠ 0 := by
    intro hiZero
    rw [hiZero] at hdominant
    simp at hdominant
  have hmargin : 3 * inputThreshold ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmodulus
  rw [hhighBudget]
  by_cases huHalf : dominantResidualRatio w i ≤ 1 / 2
  · exact sparseThresholdDominantHighActivity_lowResidual_of_cover_at
      replay.directCover hbudget w inputThreshold i hq hcentered hpositive
        hnorm hmargin hdominant huHalf
  · exact
      sparseThresholdDominantHighActivity_fourierHighResidual_of_tiltedReplay_at
        replay hbudget w inputThreshold i hq hcentered hpositive hi hdominant
          hmax (le_of_not_ge huHalf) hmargin

end CertifiedJL
