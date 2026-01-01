/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Shared.TrigonometricBernstein
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.CosineMoments
import CertifiedJL.Model.Vectors.IntegerEuclidean
import CertifiedJL.Probability.Finite.IidQuadratic
import CertifiedJL.Probability.Finite.PMF
import CertifiedJL.Analysis.Fourier.NormalizedCosineProduct
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwoDecimalAnalytic

/-!
# Shared Fourier-majorant assembly for two-decimal ternary lower bounds

The concrete cap modules prove only event geometry and the cap-dependent first
diffuse moment.  This module owns the common finite-PMF bridge, exact sparse
cosine moments, nonnegative-frequency facts, and the two normalized central
Gaussian comparisons.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL.SparseLInfLowerTwoDecimal

open Probability
open TrigonometricBernstein

noncomputable def centralPhase {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : ℝ :=
  (111 / 100 : ℝ) * Real.sqrt 2 *
    euclideanRowDot row (integerEuclideanVector w) /
      ‖integerEuclideanVector w‖

noncomputable def diffusePhase {q d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : ℝ :=
  (2 * Real.pi / (q : ℝ)) *
    euclideanRowDot row (integerEuclideanVector w)

theorem central_event_probability_toReal_le
    {d degree : ℕ} {objective : ℚ} (w : Fin d → ℤ) (hw : w ≠ 0)
    (event : (Fin d → ℤ) → Prop) [DecidablePred event]
    (fourier : List ℚ)
    (hcontract : CentralFourierContract fourier degree
      (5401 / 10000) (851 / 10000) objective)
    (hpoint : ∀ row,
      (if event row then (1 : ℝ) else 0) ≤
        rationalCosineValue fourier (centralPhase w row)) :
    (eventProbability (sparseRademacherRow d) event).toReal ≤
      (objective : ℝ) := by
  classical
  let v := integerEuclideanVector w
  have hv : v ≠ 0 := by
    intro hv0
    have hzero : sqNorm w = 0 := by
      have : ‖v‖ ^ 2 = 0 := by rw [hv0]; simp
      rw [norm_sq_integerEuclideanVector] at this
      exact_mod_cast this
    exact hw ((sqNorm_eq_zero_iff w).mp hzero)
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let p : PMF (SparseRowSeed d) := PMF.uniformOfFintype (SparseRowSeed d)
  let seedEvent : SparseRowSeed d → Prop := fun seed => event (sparseRow seed)
  have hprobSeed := finitePMF_eventProbability_toReal_le_integral p seedEvent
    (fun seed => rationalCosineValue fourier (centralPhase w (sparseRow seed)))
    (fun seed => hpoint (sparseRow seed))
  have heventMap : eventProbability (sparseRademacherRow d) event =
      eventProbability p seedEvent := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    unfold eventProbability
    rw [PMF.map_comp]
    rfl
  have hmoment (j : ℕ) :
      ∫ seed, Real.cos ((j : ℝ) * centralPhase w (sparseRow seed))
          ∂p.toMeasure =
        ∏ i, Real.cos
          ((j : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
            (w i : ℝ) / ‖v‖) ^ 2 := by
    have h := sparseRowSeed_integer_cosineMoment_eq_product w
      ((j : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / ‖v‖)
    convert h using 1
    · congr 1
      funext seed
      congr 1
      simp only [centralPhase, v]
      ring
    · apply Finset.prod_congr rfl
      intro i _
      congr 2
      ring
  have hmomentNonnegative (j : ℕ) :
      0 ≤ ∫ seed, Real.cos
        ((j : ℝ) * centralPhase w (sparseRow seed)) ∂p.toMeasure := by
    rw [hmoment]
    positivity
  have hmomentOne :
      (∫ seed, Real.cos
        ((1 : ℝ) * centralPhase w (sparseRow seed)) ∂p.toMeasure) <
        (5401 / 10000 : ℝ) := by
    rw [show (∫ seed, Real.cos
        ((1 : ℝ) * centralPhase w (sparseRow seed)) ∂p.toMeasure) =
      ∏ i, Real.cos
        ((1 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
          (w i : ℝ) / ‖v‖) ^ 2 by simpa using hmoment 1]
    have heq : (∏ i, Real.cos
        ((1 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
          (w i : ℝ) / ‖v‖) ^ 2) =
        ∏ i, Real.cos
          ((111 * Real.sqrt 2 / 200 : ℝ) * v i / ‖v‖) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i _
      congr 2
      simp only [v, integerEuclideanVector]
      ring
    rw [heq]
    have hαpi : (111 * Real.sqrt 2 / 200 : ℝ) < Real.pi / 2 := by
      have hsqrt : Real.sqrt 2 < 3 / 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_nonneg 2]
      nlinarith [Real.pi_gt_three]
    have hp := normalized_cosineProduct_le_exp_neg_sq
      v hv (by positivity) hαpi
    have hs2 : Real.sqrt 2 ^ 2 = 2 := by norm_num
    have he : (111 * Real.sqrt 2 / 200 : ℝ) ^ 2 = 12321 / 20000 := by
      rw [div_pow, mul_pow, hs2]
      norm_num
    rw [he] at hp
    exact hp.trans_lt exp_neg_lambda_sq_div_two_lt
  have hmomentTwo :
      (∫ seed, Real.cos
        ((2 : ℝ) * centralPhase w (sparseRow seed)) ∂p.toMeasure) <
        (851 / 10000 : ℝ) := by
    rw [show (∫ seed, Real.cos
        ((2 : ℝ) * centralPhase w (sparseRow seed)) ∂p.toMeasure) =
      ∏ i, Real.cos
        ((2 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
          (w i : ℝ) / ‖v‖) ^ 2 by simpa using hmoment 2]
    have heq : (∏ i, Real.cos
        ((2 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
          (w i : ℝ) / ‖v‖) ^ 2) =
        ∏ i, Real.cos
          ((111 * Real.sqrt 2 / 100 : ℝ) * v i / ‖v‖) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i _
      congr 2
      simp only [v, integerEuclideanVector]
      ring
    rw [heq]
    have hαpi : (111 * Real.sqrt 2 / 100 : ℝ) < Real.pi / 2 := by
      have hs2 : Real.sqrt 2 ^ 2 = 2 := by norm_num
      nlinarith [Real.sqrt_nonneg 2, Real.pi_gt_d2, Real.pi_pos]
    have hp := normalized_cosineProduct_le_exp_neg_sq
      v hv (by positivity) hαpi
    have hs2 : Real.sqrt 2 ^ 2 = 2 := by norm_num
    have he : (111 * Real.sqrt 2 / 100 : ℝ) ^ 2 = 12321 / 5000 := by
      rw [div_pow, mul_pow, hs2]
      norm_num
    rw [he] at hp
    exact hp.trans_lt exp_neg_two_lambda_sq_lt
  have hintegral :
      (∫ seed, rationalCosineValue fourier
          (centralPhase w (sparseRow seed)) ∂p.toMeasure) ≤ (objective : ℝ) := by
    apply integral_rationalCosineValue_le_of_centralContract
      p.toMeasure (fun seed => centralPhase w (sparseRow seed)) hcontract
    · intro j
      exact integrable_of_finitePMF p _
    · simp
    · exact hmomentNonnegative
    · norm_num at hmomentOne ⊢
      exact hmomentOne.le
    · norm_num at hmomentTwo ⊢
      exact hmomentTwo.le
  rw [heventMap]
  exact hprobSeed.trans hintegral

theorem diffuse_event_probability_toReal_le
    {q d degree : ℕ} {momentBound objective : ℚ}
    (w : Fin d → ℤ) (event : (Fin d → ℤ) → Prop) [DecidablePred event]
    (fourier : List ℚ)
    (hcontract : DiffuseFourierContract fourier degree momentBound objective)
    (hpoint : ∀ row,
      (if event row then (1 : ℝ) else 0) ≤
        rationalCosineValue fourier (diffusePhase (q := q) w row))
    (hmomentOne :
      (∫ seed, Real.cos ((1 : ℝ) *
        diffusePhase (q := q) w (sparseRow seed))
          ∂(PMF.uniformOfFintype (SparseRowSeed d)).toMeasure) ≤
        (momentBound : ℝ)) :
    (eventProbability (sparseRademacherRow d) event).toReal ≤
      (objective : ℝ) := by
  classical
  let p : PMF (SparseRowSeed d) := PMF.uniformOfFintype (SparseRowSeed d)
  let seedEvent : SparseRowSeed d → Prop := fun seed => event (sparseRow seed)
  have hprobSeed := finitePMF_eventProbability_toReal_le_integral p seedEvent
    (fun seed => rationalCosineValue fourier
      (diffusePhase (q := q) w (sparseRow seed)))
    (fun seed => hpoint (sparseRow seed))
  have heventMap : eventProbability (sparseRademacherRow d) event =
      eventProbability p seedEvent := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    unfold eventProbability
    rw [PMF.map_comp]
    rfl
  have hmoment (j : ℕ) :
      ∫ seed, Real.cos ((j : ℝ) *
          diffusePhase (q := q) w (sparseRow seed)) ∂p.toMeasure =
        ∏ i, Real.cos
          ((j : ℝ) * Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 := by
    have h := sparseRowSeed_integer_cosineMoment_eq_product w
      ((j : ℝ) * 2 * Real.pi / (q : ℝ))
    convert h using 1
    · congr 1
      funext seed
      congr 1
      simp only [diffusePhase]
      ring
    · apply Finset.prod_congr rfl
      intro i _
      congr 2
      ring
  have hmomentNonnegative (j : ℕ) :
      0 ≤ ∫ seed, Real.cos ((j : ℝ) *
        diffusePhase (q := q) w (sparseRow seed)) ∂p.toMeasure := by
    rw [hmoment]
    positivity
  have hintegral :
      (∫ seed, rationalCosineValue fourier
          (diffusePhase (q := q) w (sparseRow seed)) ∂p.toMeasure) ≤
        (objective : ℝ) := by
    apply integral_rationalCosineValue_le_of_diffuseContract p.toMeasure
      (fun seed => diffusePhase (q := q) w (sparseRow seed)) hcontract
    · intro j
      exact integrable_of_finitePMF p _
    · simp
    · exact hmomentNonnegative
    · simpa only [p] using hmomentOne
  rw [heventMap]
  exact hprobSeed.trans hintegral

end CertifiedJL.SparseLInfLowerTwoDecimal
