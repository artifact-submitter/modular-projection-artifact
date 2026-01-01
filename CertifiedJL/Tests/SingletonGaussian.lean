/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Singleton.GaussianRow
import Lean.Util.CollectAxioms

/-! # Import, boundary and trust canaries for the singleton Gaussian envelope -/

open MeasureTheory

namespace CertifiedJL.Tests.SingletonGaussian

-- Simultaneous equality at the amplitude, modulus-margin and tilt cutoffs;
-- the coefficient is negative. No odd-modulus hypothesis belongs to this lemma.
example :
    (wrappedGaussianKernel 150 (((1250 / 2401 : ℝ)) / 50 ^ 2) 0 +
      wrappedGaussianKernel 150 (((1250 / 2401 : ℝ)) / 50 ^ 2) (-49)) / 2 ≤
      singletonGaussianEnvelope (1250 / 2401) := by
  exact wrappedGaussianKernel_singleton_le_envelope (B := 50) (-49)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl

-- The scalar statement also includes the antipodal boundary 2*|z|=q.
example {t : ℝ} (ht : (1250 / 2401 : ℝ) ≤ t) :
    (wrappedGaussianKernel 6 (t / 2 ^ 2) 0 +
      wrappedGaussianKernel 6 (t / 2 ^ 2) 3) / 2 ≤
      singletonGaussianEnvelope t := by
  exact wrappedGaussianKernel_singleton_le_envelope (B := 2) 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht

-- A general two-coordinate input and arbitrary fixed shift use the selected
-- coordinate only. The other coefficient needs no centering or norm premise.
example (shift : ℤ) (w : Fin 2 → ℤ) {B t : ℝ}
    (hB : 0 < B) (hmargin : 3 * B ≤ (151 : ℝ))
    (hlarge : (49 / 50 : ℝ) * B ≤ |(w 1 : ℝ)|)
    (hcentered : 2 * |(w 1 : ℝ)| ≤ (151 : ℝ))
    (ht : (1250 / 2401 : ℝ) ≤ t) :
    (∫ row, Real.exp (-(t / B ^ 2) * affineSparseLowerRowKernel 151 shift w row)
        ∂(sparseRademacherRow 2).toMeasure) ≤ singletonGaussianEnvelope t := by
  exact sparseRow_affineCenteredGaussian_le_singletonGaussianEnvelope
    shift w 1 (by decide) hB hmargin hlarge hcentered ht

run_cmd
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name := #[
    ``realWrappedGaussianKernel_average_le_geometric,
    ``wrappedGaussianKernel_singleton_le_envelope,
    ``sparseRow_wrappedGaussianKernel_singleton_eq,
    ``sparseRow_wrappedGaussianKernel_singleton_le_envelope,
    ``sparseRow_affineCenteredGaussian_le_singletonGaussianEnvelope,
    ``sparseRow_affineCenteredGaussian_le_singletonGaussianEnvelope_of_centeredInput]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.all allowed.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.SingletonGaussian
