/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Model.Vectors.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Ring

/-!
# Exact row moment-generating functions

The finite PMFs defined by CertifiedJL become product measures through the
identities in `Model.Distributions.Entry`. Fubini's theorem therefore turns
the exponential of a row sum into a product of one-entry moment-generating
functions.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

/-- The exact moment-generating function of one sparse-Rademacher entry. -/
theorem sparseEntryMGF (t : ℝ) :
    ∫ z, Real.exp ((z : ℝ) * t) ∂sparseEntryPMF.toMeasure =
      (1 + Real.cosh t) / 2 := by
  rw [sparseEntryPMF]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (Bool × Bool)) (f := sparseBit)
    (measurable_of_finite sparseBit)]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite sparseBit)
    (measurable_of_countable
      (fun z : ℤ => Real.exp ((z : ℝ) * t))).stronglyMeasurable]
  rw [finitePMF_integral_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, sparseBit, Real.cosh_eq]
  ring

/--
The sparse-row MGF factors exactly into `(1 + cosh t) / 2` per entry.
-/
theorem sparseRowMGF {d : ℕ} (w : Fin d → ℝ) :
    ∫ row, Real.exp (realRowDot row w) ∂(sparseRademacherRow d).toMeasure =
      ∏ i, (1 + Real.cosh (w i)) / 2 := by
  rw [sparseRademacherRow_toMeasure]
  simp_rw [realRowDot, Real.exp_sum]
  simpa only [sparseEntryMGF] using
    (integral_fintype_prod_eq_prod
      (μ := fun _ : Fin d => sparseEntryPMF.toMeasure)
      (fun i (z : ℤ) => Real.exp ((z : ℝ) * w i)))

end CertifiedJL
