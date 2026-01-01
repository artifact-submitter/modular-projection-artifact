/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.FailureBudget
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Scalar assembly for even-row sparse upper endpoints

The dimension-specific radial files provide concrete Gamma and truncation
estimates.  This module packages the common algebra which turns those estimates
into a tensor lower bound at the requested failure budget.
-/

open scoped ENNReal

namespace CertifiedJL.Counterexamples.SparseUpper.EvenEndpoint

/-- Scalar parameters for the common tensor-loss calculation. -/
structure TensorData where
  rows : ℕ
  bits : ℕ
  gammaFactor : ℝ
  truncationFactor : ℝ
  lossFloor : ℝ

/-- Assemble the retained core-mass estimate from the explicit Gamma and
truncation bounds supplied by an endpoint. -/
theorem coreMass_gt (data : TensorData)
    {coreMass shiftedGamma gammaAtThreshold truncationMass radialShift : ℝ}
    (hcore : coreMass = shiftedGamma - truncationMass)
    (hgamma :
      data.gammaFactor * (2 : ℝ)⁻¹ ^ data.bits < gammaAtThreshold)
    (hshift :
      Real.exp (-radialShift) * gammaAtThreshold ≤ shiftedGamma)
    (htruncation :
      truncationMass <
        data.truncationFactor * (2 : ℝ)⁻¹ ^ data.bits) :
    coreMass >
      Real.exp (-radialShift) *
          (data.gammaFactor * (2 : ℝ)⁻¹ ^ data.bits) -
        data.truncationFactor * (2 : ℝ)⁻¹ ^ data.bits := by
  rw [hcore]
  have hgamma' :=
    mul_lt_mul_of_pos_left hgamma (Real.exp_pos (-radialShift))
  linarith

/-- The common tensor-loss calculation, including conversion of the real
`2⁻ᵇⁱᵗˢ` target to `ENNReal`. -/
theorem tensorLowerBound_gt (data : TensorData)
    {coreMass localLoss radialShift totalLoss : ℝ}
    (hlocalLoss : 0 ≤ localLoss)
    (htotalLoss :
      totalLoss = data.rows * localLoss + radialShift)
    (hcore :
      coreMass >
        Real.exp (-radialShift) *
            (data.gammaFactor * (2 : ℝ)⁻¹ ^ data.bits) -
          data.truncationFactor * (2 : ℝ)⁻¹ ^ data.bits)
    (hgammaFactor : 0 < data.gammaFactor)
    (htruncationFactor : 0 ≤ data.truncationFactor)
    (hexpLoss : data.lossFloor < Real.exp (-totalLoss))
    (hmargin :
      1 < data.gammaFactor * data.lossFloor - data.truncationFactor) :
    ENNReal.ofReal
        (Real.exp (-(data.rows : ℝ) * localLoss) * coreMass) >
      failureTarget data.bits := by
  let target : ℝ := (2 : ℝ)⁻¹ ^ data.bits
  have htargetPos : 0 < target := by
    dsimp only [target]
    positivity
  have hlocalExpPos :
      0 < Real.exp (-(data.rows : ℝ) * localLoss) := Real.exp_pos _
  have hmul := mul_lt_mul_of_pos_left hcore hlocalExpPos
  have hlocalExpLe :
      Real.exp (-(data.rows : ℝ) * localLoss) ≤ 1 := by
    have harg : -(data.rows : ℝ) * localLoss ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hlocalLoss
    simpa using (Real.exp_le_exp.mpr harg)
  have hexpCombine :
      Real.exp (-(data.rows : ℝ) * localLoss) *
          Real.exp (-radialShift) =
        Real.exp (-totalLoss) := by
    rw [← Real.exp_add, htotalLoss]
    congr 1
    ring
  have hfirst :
      data.gammaFactor * data.lossFloor * target <
        Real.exp (-totalLoss) * (data.gammaFactor * target) := by
    have hscaled := mul_lt_mul_of_pos_right hexpLoss
      (mul_pos hgammaFactor htargetPos)
    nlinarith
  have hsecond :
      Real.exp (-(data.rows : ℝ) * localLoss) *
          (data.truncationFactor * target) ≤
        data.truncationFactor * target := by
    exact mul_le_of_le_one_left
      (mul_nonneg htruncationFactor htargetPos.le) hlocalExpLe
  have hmain :
      data.gammaFactor * data.lossFloor * target -
          data.truncationFactor * target <
        Real.exp (-totalLoss) * (data.gammaFactor * target) -
          Real.exp (-(data.rows : ℝ) * localLoss) *
            (data.truncationFactor * target) := by
    linarith
  have hreal :
      target <
        Real.exp (-(data.rows : ℝ) * localLoss) * coreMass := by
    rw [mul_sub] at hmul
    rw [show
      Real.exp (-(data.rows : ℝ) * localLoss) *
          (Real.exp (-radialShift) * (data.gammaFactor * target)) =
        (Real.exp (-(data.rows : ℝ) * localLoss) *
            Real.exp (-radialShift)) *
          (data.gammaFactor * target) by ring] at hmul
    rw [hexpCombine] at hmul
    calc
      target <
          data.gammaFactor * data.lossFloor * target -
            data.truncationFactor * target := by
        nlinarith
      _ < _ := hmain
      _ < _ := hmul
  rw [failureTarget]
  have htargetENN :
      ENNReal.ofReal target = (2 : ENNReal)⁻¹ ^ data.bits := by
    dsimp only [target]
    rw [ENNReal.ofReal_pow
      (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) data.bits]
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← htargetENN]
  have hright :
      0 < Real.exp (-(data.rows : ℝ) * localLoss) * coreMass :=
    htargetPos.trans hreal
  exact (ENNReal.ofReal_lt_ofReal_iff hright).2 hreal

end CertifiedJL.Counterexamples.SparseUpper.EvenEndpoint
