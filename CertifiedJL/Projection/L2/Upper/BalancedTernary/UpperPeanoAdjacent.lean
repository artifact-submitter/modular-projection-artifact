/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoHybridProducts
import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherScaled

/-! # Concrete adjacent step of the sparse upper Peano telescope -/

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

/-- Once the two concrete hybrid product integrals are split over their common
rest-sum law, the adjacent coordinate replacement is exactly the lifted
fourth-Peano identity. -/
theorem upperPeanoHybridValue_adjacent_fourthPeano
    {n : ℕ} (b : Fin n → ℝ) (s : ℂ) (i : Fin n) (ρ : Measure ℝ)
    (hscale : 2 * b i ^ 2 * s.re < 1)
    (hG : Integrable (fun w =>
      ∫ y : ℝ, complexQuadraticExp s (w + b i * y) ∂gaussianReal 0 1) ρ)
    (hR : Integrable (fun w =>
      ∫ y : ℝ, complexQuadraticExp s (w + b i * y)
        ∂standardRademacherMeasure) ρ)
    (hbefore : upperPeanoHybridValue b s i.val =
      ∫ w, ∫ y : ℝ, complexQuadraticExp s (w + b i * y)
        ∂gaussianReal 0 1 ∂ρ)
    (hafter : upperPeanoHybridValue b s (i.val + 1) =
      ∫ w, ∫ y : ℝ, complexQuadraticExp s (w + b i * y)
        ∂standardRademacherMeasure ∂ρ) :
    upperPeanoHybridValue b s i.val -
        upperPeanoHybridValue b s (i.val + 1) =
      (b i ^ 4 / 12 : ℝ) •
        ∫ w, ∫ k : ℝ,
          iteratedDeriv 4 (complexQuadraticExp s) (w + b i * k)
            ∂peanoKMeasure ∂ρ := by
  rw [hbefore, hafter]
  exact peanoIdentity4_partialSum_standardGaussianRademacher_scaled
    (b i) hscale hG hR

end CertifiedJL
