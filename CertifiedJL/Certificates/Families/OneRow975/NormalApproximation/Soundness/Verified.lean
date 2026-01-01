/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Assembly
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs

/-!
# Verified bounded `3/5` tilted-Rademacher normal approximation

This module exports the analytic results obtained from the retained 24-cell
moderate-Lyapunov certificate. Individual cell proof modules import only
`CertificateData.Soundness` and the sole retained data shard; the aggregate
proof module assembles their semantic certificates here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CertifiedJL
namespace Probability

universe u

/--
The retained moderate grid supplies valid Prawitz cutoffs and proves
`D* < 3/5` throughout `[1/50, 19707/100000]`.
-/
theorem tyurinRationalDStar_lt_three_fifths_of_moderate
    {L : ℝ} (hlo : (1 : ℝ) / 50 ≤ L)
    (hhi : L ≤ (19707 : ℝ) / 100000) :
    ∃ U₀ U : ℝ, 0 < U₀ ∧ U₀ ≤ U ∧
      tyurinRationalDStar L U₀ U < (3 : ℝ) / 5 :=
  TyurinModerate.moderateCutoffs_of_gridCertified
    TyurinModerate.moderateGridCells_certified hlo hhi

/--
Coefficient-uniform Berry--Esseen estimate with the exact constant `3/5`,
on the bounded Lyapunov range actually needed by the one-row and zero-tilt
applications.
-/
theorem rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_lyapunov_le
    {ι : Type u} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hL : rademacherLyapunovRatio b x ≤ (19707 : ℝ) / 100000) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * rademacherLyapunovRatio b x :=
  TyurinModerate.rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_gridCertified_of_le
    TyurinModerate.moderateGridCells_certified b x hnorm hL

end Probability
end CertifiedJL
