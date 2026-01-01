/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.ClosedCoreFirstBox

/-!
# Experimental closed-core first-box kernel provider

This opt-in replay evaluates 140 coarse suffix cells. It is deliberately
outside the production and Fast import closures: the route has not yet been
split into cataloged bounded leaves or established to improve total replay time.
-/

open MeasureTheory Set

namespace CertifiedJL.SparseUpperContour.ClosedCore

set_option maxRecDepth 100000

theorem firstBoxCoarseClosedBudget : FirstBoxCoarseClosedBudget := by
  unfold FirstBoxCoarseClosedBudget
  decide +kernel

/-- The original strict endpoint supplied by the experimental kernel replay. -/
theorem firstBox_coarse_closed_endpoint
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    boxActualPrefactorValue (profileBox 0) *
      (∫ frequency : ℝ in Set.Ioi 0,
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) <
      (97 / 100 : ℝ) :=
  firstBox_coarse_closed_endpoint_of_budget firstBoxCoarseClosedBudget hprofile

end CertifiedJL.SparseUpperContour.ClosedCore
