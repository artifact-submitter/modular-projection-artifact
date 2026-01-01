/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author

This proof is adapted from
`MathExtras/NumberTheory/Analysis/VaalerJhatCornerLimits.lean` in
`gersh/ternary-goldbach-lean`, commit
`89416190c037331d7ebc04cd62ddb974cfb4dfcf` (Apache-2.0),
copyright (c) 2026 Gershon Bialer.
-/

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Smoothness of the real sinc function

Mathlib currently provides continuity of `Real.sinc`, but the Vaaler
two-integration-by-parts argument needs two derivatives at its removable
zero.  The divided-difference representation of sinc upgrades it to a
real-analytic, hence smooth, function.
-/

open Filter
open scoped ContDiff

namespace CertifiedJL
namespace Probability

theorem analyticAt_realSinc (x : ℝ) :
    AnalyticAt ℝ Real.sinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := 0)
    rw [Real.sinc_eq_dslope]
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have hden : AnalyticAt ℝ (fun y : ℝ => y) x := analyticAt_id
    have hnum : AnalyticAt ℝ Real.sin x := Real.analyticAt_sin
    have hquot :
        AnalyticAt ℝ (fun y : ℝ => Real.sin y / y) x :=
      hnum.div hden hx
    refine hquot.congr ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (Real.sinc_of_ne_zero hy).symm

theorem contDiff_realSinc :
    ContDiff ℝ ∞ Real.sinc :=
  contDiff_iff_contDiffAt.2
    (fun x => (analyticAt_realSinc x).contDiffAt.of_le le_top)

end Probability
end CertifiedJL
