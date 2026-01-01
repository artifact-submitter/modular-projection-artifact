/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Rademacher.TiltedRademacherCharacteristic
import CertifiedJL.Probability.Distributions.Rademacher.RademacherEsscherBound

/-!
# Bridge between the Esscher and characteristic-function tilted laws

The Esscher layer uses the tilt `uᵢ = x bᵢ` and presents the standardized
law as two successive measure maps.  The characteristic-function layer uses
the same finite product PMF and one centered, normalized map.  This file proves
that the two presentations are definitionally the same mathematical object.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL
namespace Probability

theorem tiltedRademacherVariance_specialize
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    tiltedRademacherVariance (fun i => x * b i) b =
      rademacherTiltedVariance b x := by
  unfold tiltedRademacherVariance rademacherTiltedVariance
  apply Finset.sum_congr rfl
  intro i _
  rw [one_sub_tanh_sq]

theorem tiltedRademacherStdDev_specialize
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    tiltedRademacherStdDev (fun i => x * b i) b =
      rademacherTiltedStdDev b x := by
  unfold tiltedRademacherStdDev rademacherTiltedStdDev
  rw [tiltedRademacherVariance_specialize]

theorem standardizedTiltedRademacherSum_specialize
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (bits : ι → Bool) :
    standardizedTiltedRademacherSum (fun i => x * b i) b bits =
      (rademacherSum b bits - rademacherTiltedMean b x) /
        rademacherTiltedStdDev b x := by
  unfold standardizedTiltedRademacherSum rademacherSum
    rademacherTiltedMean
  rw [tiltedRademacherStdDev_specialize]
  simp_rw [biasedSignValue_eq_signBit]
  rw [show
      (∑ i, b i / rademacherTiltedStdDev b x *
          ((signBit (bits i) : ℝ) - Real.tanh (x * b i))) =
        (∑ i, b i *
          ((signBit (bits i) : ℝ) - Real.tanh (x * b i))) /
            rademacherTiltedStdDev b x by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  congr 1
  calc
    (∑ i, b i *
        ((signBit (bits i) : ℝ) - Real.tanh (x * b i))) =
        ∑ i, (b i * (signBit (bits i) : ℝ) -
          b i * Real.tanh (x * b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, b i * (signBit (bits i) : ℝ)) -
        ∑ i, b i * Real.tanh (x * b i) := by
      rw [← Finset.sum_sub_distrib]
    _ = (∑ i, (signBit (bits i) : ℝ) * b i) -
        ∑ i, b i * Real.tanh (x * b i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem standardizedTiltedRademacherPMF_toMeasure_specialize
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    (standardizedTiltedRademacherPMF (fun i => x * b i) b).toMeasure =
      rademacherTiltedStandardizedLaw b x := by
  rw [standardizedTiltedRademacherPMF_toMeasure]
  unfold rademacherTiltedStandardizedLaw rademacherTiltedSumLaw
  rw [Measure.map_map]
  · congr 1
    funext bits
    exact standardizedTiltedRademacherSum_specialize b x bits
  · fun_prop
  · exact measurable_of_finite _

theorem charFun_rademacherTiltedStandardizedLaw_eq_prod
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x t : ℝ) :
    charFun (rademacherTiltedStandardizedLaw b x) t =
      ∏ i, centeredBiasedSignChar
        (x * b i) (b i / rademacherTiltedStdDev b x) t := by
  rw [← standardizedTiltedRademacherPMF_toMeasure_specialize b x,
    charFun_standardizedTiltedRademacherPMF_eq_prod]
  simp only [tiltedRademacherStdDev_specialize]

end Probability
end CertifiedJL
