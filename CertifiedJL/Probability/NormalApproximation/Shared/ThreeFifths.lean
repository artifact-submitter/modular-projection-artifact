/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.PrawitzBridge
import CertifiedJL.Probability.NormalApproximation.Tyurin.SmallLyapunov

/-!
# Local ingredients for bounded `3/5` normal approximation

The sharp Prawitz bridge reduces the tilted-Rademacher Kolmogorov estimate to
an explicit `D*` bound. This file exposes only the local certified-`D*` bridge
and the analytic small-Lyapunov branch needed by the bounded one-row assembly.
-/

open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace Probability

section TiltedRademacherAssembly

open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι]

/--
Any strict `D* < 3/5` certificate at valid Prawitz cutoffs yields the desired
linear Kolmogorov estimate for the actual standardized tilted-Rademacher law.
All characteristic-function and moment premises have already been discharged
by `TyurinPrawitzBridge`.
-/
theorem
    rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_dstar_lt
    (b : ι → ℝ) (x : ℝ) (hnorm : ∑ i, b i ^ 2 = 1)
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hcut : U₀ ≤ U)
    (hDStar :
      tyurinRationalDStar (rademacherLyapunovRatio b x) U₀ U <
        (3 : ℝ) / 5) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * rademacherLyapunovRatio b x := by
  have hL :
      0 < rademacherLyapunovRatio b x :=
    rademacherLyapunovRatio_pos b x hnorm
  have hbase :=
    kolmogorovDistance_rademacherTiltedStandardizedLaw_le_mul_tyurinRationalDStar
      b x hnorm hU₀ hcut
  nlinarith

/--
The complete small-Lyapunov branch of the coefficient-uniform
tilted-Rademacher Berry--Esseen theorem.
-/
theorem
    rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_small
    (b : ι → ℝ) (x : ℝ) (hnorm : ∑ i, b i ^ 2 = 1)
    (hsmall : rademacherLyapunovRatio b x ≤ 1 / 50) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * rademacherLyapunovRatio b x := by
  let L := rademacherLyapunovRatio b x
  have hL : 0 < L :=
    rademacherLyapunovRatio_pos b x hnorm
  have hU₀ :
      0 < tyurinSmallBranchCutoff L :=
    small_branchCutoff_pos hL
  have hcut :
      tyurinSmallBranchCutoff L ≤ tyurinSmallBandwidth L := by
    exact
      (small_branchCutoff_le_inv hL hsmall).trans
        ((div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hL.le).trans
          (small_two_inv_le_bandwidth hL))
  apply
    rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_dstar_lt
      b x hnorm hU₀ hcut
  exact tyurinRationalDStar_lt_three_fifths_of_small hL hsmall

end TiltedRademacherAssembly

end Probability
end CertifiedJL
