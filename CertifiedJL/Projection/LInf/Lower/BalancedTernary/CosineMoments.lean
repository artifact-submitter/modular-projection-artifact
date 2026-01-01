/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.GaussianFourier
import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Model.Vectors.IntegerEuclidean

/-!
# Periodic cosine identities for sparse integer rows

These endpoint-independent identities connect sparse integer row sums, their
Euclidean casts, the uniform sparse-row seed, and centered modular reduction.
-/

open scoped BigOperators
open MeasureTheory

namespace CertifiedJL

/-- The sparse-row cosine moment factors as a product of cosine squares. -/
theorem sparseRademacherRow_integer_cosineMoment_eq_product {d : ℕ}
    (w : Fin d → ℤ) (t : ℝ) :
    ∫ row, Real.cos (t * euclideanRowDot row (integerEuclideanVector w))
        ∂(sparseRademacherRow d).toMeasure =
      ∏ i, Real.cos (t * (w i : ℝ) / 2) ^ 2 := by
  have h := sparseRow_cosineTransform d t (fun i => (w i : ℝ))
  convert h using 1
  · congr 1
  · apply Finset.prod_congr rfl
    intro i _
    calc
      Real.cos (t * (w i : ℝ) / 2) ^ 2 =
          (1 + Real.cos (2 * (t * (w i : ℝ) / 2))) / 2 := by
            rw [Real.cos_two_mul]
            ring
      _ = (1 + Real.cos (t * (w i : ℝ))) / 2 := by congr 2 <;> ring

/-- The uniform sparse-row seed has the same factored cosine moment. -/
theorem sparseRowSeed_integer_cosineMoment_eq_product {d : ℕ}
    (w : Fin d → ℤ) (t : ℝ) :
    ∫ seed, Real.cos
        (t * euclideanRowDot (sparseRow seed) (integerEuclideanVector w))
        ∂(PMF.uniformOfFintype (SparseRowSeed d)).toMeasure =
      ∏ i, Real.cos (t * (w i : ℝ) / 2) ^ 2 := by
  let p : PMF (SparseRowSeed d) := PMF.uniformOfFintype (SparseRowSeed d)
  have hmap :
      (∫ seed, Real.cos
          (t * euclideanRowDot (sparseRow seed) (integerEuclideanVector w))
          ∂p.toMeasure) =
        ∫ row, Real.cos
          (t * euclideanRowDot row (integerEuclideanVector w))
          ∂(sparseRademacherRow d).toMeasure := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    rw [← PMF.toMeasure_map (p := p) (f := @sparseRow d)
      (measurable_of_finite sparseRow)]
    rw [integral_map_of_stronglyMeasurable (measurable_of_finite sparseRow)
      (measurable_of_countable
        (fun row : Fin d → ℤ => Real.cos
          (t * euclideanRowDot row (integerEuclideanVector w)))).stronglyMeasurable]
  exact hmap.trans (sparseRademacherRow_integer_cosineMoment_eq_product w t)

/-- Centered modular reduction preserves the basic `2π/q` cosine phase. -/
theorem cosine_twoPiOverModulus_centeredMod
    {q : ℕ} (hq : q ≠ 0) (z : ℤ) :
    Real.cos ((2 * Real.pi / (q : ℝ)) * (z : ℝ)) =
      Real.cos ((2 * Real.pi / (q : ℝ)) * (centeredMod q z : ℝ)) := by
  let : NeZero q := ⟨hq⟩
  have hcong :
      (centeredMod q z : ZMod q) = (z : ZMod q) :=
    centeredMod_intCast q z
  have hdiv : (q : ℤ) ∣ z - centeredMod q z :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (centeredMod q z) z q).mp hcong
  obtain ⟨n, hn⟩ := hdiv
  have hnReal :
      (z : ℝ) - (centeredMod q z : ℝ) = (q : ℝ) * (n : ℝ) := by
    exact_mod_cast hn
  have hphase :
      (2 * Real.pi / (q : ℝ)) * (z : ℝ) =
        (2 * Real.pi / (q : ℝ)) * (centeredMod q z : ℝ) +
          (n : ℝ) * (2 * Real.pi) := by
    have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    field_simp [hqReal]
    nlinarith [Real.pi_pos]
  rw [hphase, Real.cos_add_int_mul_two_pi]

end CertifiedJL
