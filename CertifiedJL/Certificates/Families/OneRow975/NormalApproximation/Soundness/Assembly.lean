/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.GridCoverage
import CertifiedJL.Probability.NormalApproximation.Shared.ThreeFifths

/-!
# Assembly from the one-row moderate grid to the `3/5` theorem

This module isolates the inexpensive logical assembly from the generated
kernel-checked cell certificates.  The only premise is semantic certification
of every cell in the committed moderate grid.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CertifiedJL
namespace TyurinModerate

universe u

/--
Semantic certification of the committed grid completes the `3/5`
normal-approximation theorem whenever the tilted Lyapunov ratio is at most
the one-row profile cap `19707/100000`.
-/
theorem
    rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_gridCertified_of_le
    (hcertified : ∀ C ∈ moderateGridCells, CellCertified C)
    {ι : Type u} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hupper : Probability.rademacherLyapunovRatio b x ≤
      (19707 : ℝ) / 100000) :
    Probability.kolmogorovDistance
        (Probability.rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * Probability.rademacherLyapunovRatio b x := by
  let L := Probability.rademacherLyapunovRatio b x
  by_cases hsmall : L ≤ (1 : ℝ) / 50
  · exact
      Probability.rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_small
        b x hnorm hsmall
  obtain ⟨U₀, U, hU₀, hcut, hDStar⟩ :=
    moderateCutoffs_of_gridCertified hcertified
      (le_of_lt (lt_of_not_ge hsmall)) hupper
  exact
    Probability.rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_dstar_lt
      b x hnorm hU₀ hcut hDStar

end TyurinModerate
end CertifiedJL
