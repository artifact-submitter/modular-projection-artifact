/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.EvenGaussianComparison

/-!
# Radial-tail decomposition for even-row upper endpoints

This module splits the strict half-Gaussian radial tail into the bounded core
used by the mesh comparison and its coordinate-truncation remainder.
-/

open scoped BigOperators
open MeasureTheory

namespace CertifiedJL.Counterexamples.SparseUpper.EvenRadialEndpoint

open CertifiedJL.Probability
open EvenGaussian.Internal

variable {rows shape : ℕ}

/-- The strict radial tail above the shifted endpoint. -/
def gaussianRadialTail (threshold : ℕ) : Set (Fin rows → ℝ) :=
  {x | radialThreshold (rows := rows) threshold <
    HalfGaussianEven.squaredRadius x}

theorem measurableSet_gaussianRadialTail (threshold : ℕ) :
    MeasurableSet (gaussianRadialTail (rows := rows) threshold) := by
  unfold gaussianRadialTail HalfGaussianEven.squaredRadius
  exact measurableSet_lt measurable_const
    (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).pow_const 2)

/-- The strict radial tail is the disjoint union of the bounded mesh core and
the part removed by the coordinate cutoff. -/
theorem gaussianRadialTail_eq_union (threshold : ℕ) :
    gaussianRadialTail (rows := rows) threshold =
      gaussianCore (rows := rows) threshold ∪
        HalfGaussianEven.halfGaussianTruncationSet
          (radialThreshold (rows := rows) threshold) coordinateBound := by
  ext x
  simp only [gaussianRadialTail, gaussianCore,
    HalfGaussianEven.halfGaussianTruncationSet, Set.mem_ofPred_eq,
    Set.mem_union]
  constructor
  · intro hradial
    by_cases hcoord : ∀ j, |x j| < coordinateBound
    · exact Or.inl ⟨hradial, hcoord⟩
    · push Not at hcoord
      exact Or.inr ⟨hradial, hcoord⟩
  · rintro (h | h) <;> exact h.1

theorem gaussianCore_disjoint_truncation (threshold : ℕ) :
    Disjoint (gaussianCore (rows := rows) threshold)
      (HalfGaussianEven.halfGaussianTruncationSet
        (radialThreshold (rows := rows) threshold) coordinateBound) := by
  rw [Set.disjoint_left]
  intro x hxCore hxTail
  obtain ⟨j, hj⟩ := hxTail.2
  exact (not_lt_of_ge hj) (hxCore.2 j)

/-- Integral form of the radial-tail decomposition.  The row/shape relation
and positivity assumptions are explicit at every endpoint specialization. -/
theorem integral_gaussianCore_eq_gamma_sub_truncation
    (threshold : ℕ) (hrows : rows = 2 * shape) (hshape : 0 < shape)
    (hthreshold :
      0 ≤ radialThreshold (rows := rows) threshold) :
    (∫ x : Fin rows → ℝ in gaussianCore (rows := rows) threshold,
        HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat shape (radialThreshold (rows := rows) threshold) -
        ∫ x : Fin rows → ℝ in
          HalfGaussianEven.halfGaussianTruncationSet
            (radialThreshold (rows := rows) threshold) coordinateBound,
          HalfGaussianEven.halfGaussianProductDensity x := by
  have hunion :=
    setIntegral_union (gaussianCore_disjoint_truncation (rows := rows) threshold)
      (HalfGaussianEven.measurableSet_halfGaussianTruncationSet
        (radialThreshold (rows := rows) threshold) coordinateBound)
      HalfGaussianEven.integrable_halfGaussianProductDensity.integrableOn
      HalfGaussianEven.integrable_halfGaussianProductDensity.integrableOn
  rw [← gaussianRadialTail_eq_union (rows := rows) threshold] at hunion
  have htail :
      (∫ x : Fin rows → ℝ in gaussianRadialTail (rows := rows) threshold,
          HalfGaussianEven.halfGaussianProductDensity x) =
        gammaSurvivalNat shape
          (radialThreshold (rows := rows) threshold) := by
    simpa [gaussianRadialTail, HalfGaussianEven.squaredRadius] using
      (HalfGaussianEven.integral_halfGaussianProductDensity_tail
        hrows hshape hthreshold)
  rw [htail] at hunion
  linarith

end CertifiedJL.Counterexamples.SparseUpper.EvenRadialEndpoint
