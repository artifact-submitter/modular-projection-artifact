/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.CosineLaplace
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.Scalar.LobeTail
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier
import CertifiedJL.Analysis.Fourier.LowerPeriodization
import Mathlib.Tactic.NormNum

/-!
# High-mass diffuse threshold profiles

This file closes the part of the compact diffuse profile where the selected
squared mass is at least `11/10` of the public threshold squared.  The key
point is to retain the coupling between the normalized tilt `s` and every
Hölder exponent `p`: the `3/4` coordinate cap gives `p >= (320/297) s`.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

private theorem thresholdDiffuse_modularExponent_eq
    {B Q V : ℝ} (hB : 0 < B) (hV : 0 < V) :
    ((33 / 10 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (33 / 10 : ℝ) * V / B ^ 2) =
      (33 / 10 : ℝ) * Q ^ 2 / (B ^ 2 + (33 / 10 : ℝ) * V) := by
  have hsqrt : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  field_simp [hB.ne', hsqrt_ne]
  rw [hsqrt]
  field_simp [hV.ne']

private theorem thresholdDiffuse_first_modularExponent_ge
    {B Q V : ℝ} (hB : 0 < B) (hV : 0 < V)
    (hQ : 3 * B ≤ Q) (hVupper : V ≤ (6 / 5 : ℝ) * B ^ 2) :
    (1485 / 248 : ℝ) ≤
      ((33 / 10 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (33 / 10 : ℝ) * V / B ^ 2) := by
  rw [thresholdDiffuse_modularExponent_eq hB hV]
  have hQ2 : 9 * B ^ 2 ≤ Q ^ 2 := by nlinarith [sq_nonneg (Q - 3 * B)]
  have hden : 0 < B ^ 2 + (33 / 10 : ℝ) * V := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem thresholdDiffuse_second_modularExponent_ge
    {B Q V : ℝ} (hB : 0 < B) (hV : 0 < V)
    (hQ : 3 * B ≤ Q) (hVupper : V ≤ (25 / 16 : ℝ) * B ^ 2) :
    (4752 / 985 : ℝ) ≤
      ((33 / 10 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (33 / 10 : ℝ) * V / B ^ 2) := by
  rw [thresholdDiffuse_modularExponent_eq hB hV]
  have hQ2 : 9 * B ^ 2 ≤ Q ^ 2 := by nlinarith [sq_nonneg (Q - 3 * B)]
  have hden : 0 < B ^ 2 + (33 / 10 : ℝ) * V := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The coupled scalar-lobe estimate tensorizes over a normalized sparse row. -/
theorem sparseRow_nonmodulated_le_lobe_of_tilt_ratio
    {d : ℕ} (a : Fin d → ℝ) (S : Finset (Fin d))
    (hS : ∀ i, i ∈ S ↔ a i ≠ 0)
    (ha : ∑ i, a i ^ 2 = 1)
    {s sLower r : ℝ} (hsLower : 0 < sLower) (hs : sLower ≤ s)
    (hr : 0 < r) (hcap : ∀ i, r * s * a i ^ 2 ≤ 2) :
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (1 / Real.sqrt (1 + sLower) *
          (1 + 2 * Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
            (1 - (Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3))) := by
  have hreduce := sparseScalarReduction s a S hS (hsLower.le.trans hs) ha
  refine hreduce.trans ?_
  let C : ℝ := 1 / Real.sqrt (1 + sLower) *
    (1 + 2 * Real.exp
        (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
      (1 - (Real.exp
        (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3))
  have hC : 0 ≤ C := by
    dsimp [C]
    have hc : 0 < r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)) := by
      positivity
    have hx : Real.exp
        (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    have hx3 : Real.exp
        (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) ^ 3 < 1 :=
      pow_lt_one₀ (Real.exp_nonneg _) hx (by norm_num)
    positivity
  calc
    (∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2)) ≤
        ∏ i ∈ S, ENNReal.ofReal C ^ (a i ^ 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hai_pos : 0 < a i ^ 2 := by
          have hai : a i ≠ 0 := (hS i).1 hi
          positivity
        have hp : r * s ≤ 2 / (a i ^ 2) := by
          exact (le_div_iff₀ hai_pos).2 (hcap i)
        have hp_pos : 0 < 2 / (a i ^ 2) := by positivity
        have hmoment : gaussianCosineMoment s (2 / (a i ^ 2)) ≤
            ENNReal.ofReal C := by
          rw [gaussianCosineMoment_eq_ofReal_sparseScalarF hp_pos]
          exact ENNReal.ofReal_mono
            (sparseScalarF_lobe_periodization_of_tilt_ratio
              hsLower hs hr hp)
        exact ENNReal.rpow_le_rpow hmoment (sq_nonneg (a i))
    _ = ENNReal.ofReal (∏ i ∈ S, C ^ (a i ^ 2)) := by
      simp_rw [ENNReal.ofReal_rpow_of_nonneg hC (sq_nonneg (a _))]
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro i hi
      positivity
    _ = ENNReal.ofReal C := by
      congr 1
      rw [← Real.rpow_sum_of_nonneg hC (fun i hi => sq_nonneg (a i))]
      have hsumS : ∑ i ∈ S, a i ^ 2 = 1 := by
        calc
          ∑ i ∈ S, a i ^ 2 = ∑ i, a i ^ 2 := by
            apply Finset.sum_subset (by simp)
            intro i hi hnot
            have hai_zero : a i = 0 := by
              by_contra hai
              exact hnot ((hS i).2 hai)
            simp [hai_zero]
          _ = 1 := ha
      rw [hsumS, Real.rpow_one]
    _ = ENNReal.ofReal
        (1 / Real.sqrt (1 + sLower) *
          (1 + 2 * Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
            (1 - (Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3))) := by
      rfl

/-- Normalized integer-profile form of the coupled zero-image estimate. -/
theorem sparseRow_normalized_nonmodulated_le_lobe_of_tilt_ratio
    {d : ℕ} (w : Fin d → ℤ) (V : ℝ)
    (hV : 0 < V) (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    {s sLower r : ℝ} (hsLower : 0 < sLower) (hs : sLower ≤ s)
    (hr : 0 < r) (hcap : ∀ i, r * s * (w i : ℝ) ^ 2 ≤ 2 * V) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (1 / Real.sqrt (1 + sLower) *
          (1 + 2 * Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
            (1 - (Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3))) := by
  let a : Fin d → ℝ := fun i ↦ (w i : ℝ) / Real.sqrt V
  let S : Finset (Fin d) := Finset.univ.filter fun i ↦ a i ≠ 0
  have hsqrt_sq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hS : ∀ i, i ∈ S ↔ a i ≠ 0 := by intro i; simp [S]
  have ha : ∑ i, a i ^ 2 = 1 := by
    calc
      ∑ i, a i ^ 2 = ∑ i, (w i : ℝ) ^ 2 / V := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [a]
        rw [div_pow, hsqrt_sq]
      _ = (∑ i, (w i : ℝ) ^ 2) / V := by rw [Finset.sum_div]
      _ = V / V := by rw [h_norm]
      _ = 1 := div_self hV.ne'
  have hcap_a : ∀ i, r * s * a i ^ 2 ≤ 2 := by
    intro i
    dsimp [a]
    rw [div_pow, hsqrt_sq]
    rw [show r * s * ((w i : ℝ) ^ 2 / V) =
      (r * s * (w i : ℝ) ^ 2) / V by ring]
    exact (div_le_iff₀ hV).2 (by simpa [mul_assoc] using hcap i)
  have hdot (row : Fin d → ℤ) :
      realRowDot row a =
        ((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V := by
    simp only [realRowDot, a, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [hdot] using sparseRow_nonmodulated_le_lobe_of_tilt_ratio
    a S hS ha hsLower hs hr hcap_a

/-- Normalized modular form of the coupled diffuse row estimate. -/
theorem sparseRow_normalizedPeriodization_le_lobe_of_tilt_ratio
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (V : ℝ)
    (hq : Odd q) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    {s sLower r : ℝ} (hsLower : 0 < sLower) (hs : sLower ≤ s)
    (hr : 0 < r) (hcap : ∀ i, r * s * (w i : ℝ) ^ 2 ≤ 2 * V) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (1 / Real.sqrt (1 + sLower) *
          (1 + 2 * Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
            (1 - (Real.exp
              (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3))) +
      ENNReal.ofReal
        (2 * Real.exp
          (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := by
  let a : Fin d → ℝ := fun i => (w i : ℝ) / Real.sqrt V
  let S : Finset (Fin d) := Finset.univ.filter fun i => a i ≠ 0
  have hsqrt_sq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hS : ∀ i, i ∈ S ↔ a i ≠ 0 := by
    intro i
    simp [S]
  have ha : ∑ i, a i ^ 2 = 1 := by
    calc
      ∑ i, a i ^ 2 = ∑ i, (w i : ℝ) ^ 2 / V := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [a]
        rw [div_pow, hsqrt_sq]
      _ = (∑ i, (w i : ℝ) ^ 2) / V := by
        rw [Finset.sum_div]
      _ = V / V := by rw [h_norm]
      _ = 1 := div_self hV.ne'
  have hcap_a : ∀ i, r * s * a i ^ 2 ≤ 2 := by
    intro i
    dsimp [a]
    rw [div_pow, hsqrt_sq]
    rw [show r * s * ((w i : ℝ) ^ 2 / V) =
      (r * s * (w i : ℝ) ^ 2) / V by ring]
    apply (div_le_iff₀ hV).2
    simpa [mul_assoc] using hcap i
  have hdot (row : Fin d → ℤ) :
      realRowDot row a =
        ((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V := by
    simp only [realRowDot, a, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hzero := sparseRow_nonmodulated_le_lobe_of_tilt_ratio
    a S hS ha hsLower hs hr hcap_a
  have hzero' :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V) ^ 2)
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal
          (1 / Real.sqrt (1 + sLower) *
            (1 + 2 * Real.exp
                (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
              (1 - (Real.exp
                (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3))) := by
    simpa only [hdot] using hzero
  have hperiod := sparseRow_normalizedPeriodization_nonzeroImageBound
    w q V s hq hV h_norm (hsLower.trans_le hs)
  exact hperiod.trans (add_le_add hzero' le_rfl)

/-- The compact diffuse row is below `97/200` throughout the high selected-mass
band `11 B²/10 ≤ V < 25 B²/16`.  The proof splits once at `6 B²/5`: below
that point the tighter modular tail is paired with tilt `363/100`; above it,
tilt `99/25` has enough Gaussian normalization to absorb the larger wrap tail. -/
theorem sparseRow_diffuse_highMass_normalized_le_97_div_200
    (replay : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128)
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (B V : ℝ)
    (hq : Odd q) (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hmargin : 3 * B ≤ (q : ℝ))
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : (11 / 10 : ℝ) * B ^ 2 ≤ V)
    (hVupper : V ≤ (25 / 16 : ℝ) * B ^ 2) :
    ∫ row, Real.exp
        (-((33 / 10 : ℝ) * V / B ^ 2) *
          ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
        ∂(sparseRademacherRow d).toMeasure ≤
      97 / 200 := by
  let s : ℝ := (33 / 10 : ℝ) * V / B ^ 2
  have hs_pos : 0 < s := by dsimp [s]; positivity
  have hcap : ∀ i, (320 / 297 : ℝ) * s * (w i : ℝ) ^ 2 ≤ 2 * V := by
    intro i
    have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
    rw [show (320 / 297 : ℝ) * s * (w i : ℝ) ^ 2 =
      ((320 / 297 : ℝ) * (33 / 10) * V * (w i : ℝ) ^ 2) /
        B ^ 2 by dsimp [s]; ring]
    apply (div_le_iff₀ hBsq).2
    have hmul := mul_le_mul_of_nonneg_left (hdiffuse i) hV.le
    nlinarith
  by_cases hfirst : V ≤ (6 / 5 : ℝ) * B ^ 2
  · have hsLower : (363 / 100 : ℝ) ≤ s := by
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      dsimp [s]
      apply (le_div_iff₀ hBsq).2
      nlinarith
    have hcert := sparseRow_normalizedPeriodization_le_lobe_of_tilt_ratio
      w q V hq hV h_norm (s := s) (sLower := (363 / 100 : ℝ))
        (r := (320 / 297 : ℝ)) (by norm_num) hsLower (by norm_num) hcap
    have hmodExponent := thresholdDiffuse_first_modularExponent_ge
      hB hV hmargin hfirst
    have hmodTail := replay.firstTail hmodExponent
    have hmodTail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3) <
          (1 / 198 : ℝ) := by
      dsimp [s]
      convert hmodTail using 1
      all_goals ring_nf
    have henn : ENNReal.ofReal
          (∫ row, Real.exp
            (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
              Real.sqrt V) ^ 2)
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (97 / 200 : ℝ) := by
      calc
        _ ≤ ENNReal.ofReal
              (1 / Real.sqrt (1 + (363 / 100 : ℝ)) *
                (1 + 2 * Real.exp
                    (-((320 / 297 : ℝ) * (363 / 100) * Real.pi ^ 2 /
                      (2 * (1 + (363 / 100))))) /
                  (1 - (Real.exp
                    (-((320 / 297 : ℝ) * (363 / 100) * Real.pi ^ 2 /
                      (2 * (1 + (363 / 100)))))) ^ 3))) +
            ENNReal.ofReal
              (2 * Real.exp
                (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
                (1 - (Real.exp
                  (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) :=
            hcert
        _ ≤ ENNReal.ofReal (2399 / 5000 : ℝ) +
            ENNReal.ofReal (1 / 198 : ℝ) :=
          add_le_add
            (ENNReal.ofReal_mono replay.firstLobe.le)
            (ENNReal.ofReal_mono hmodTail'.le)
        _ = ENNReal.ofReal
            ((2399 / 5000 : ℝ) + (1 / 198 : ℝ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (97 / 200 : ℝ) := by
          exact ENNReal.ofReal_mono (by norm_num)
    simpa only [s] using
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 97 / 200)).mp henn
  · have hsecond : (6 / 5 : ℝ) * B ^ 2 ≤ V := le_of_not_ge hfirst
    have hsLower : (99 / 25 : ℝ) ≤ s := by
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      dsimp [s]
      apply (le_div_iff₀ hBsq).2
      nlinarith
    have hcert := sparseRow_normalizedPeriodization_le_lobe_of_tilt_ratio
      w q V hq hV h_norm (s := s) (sLower := (99 / 25 : ℝ))
        (r := (320 / 297 : ℝ)) (by norm_num) hsLower (by norm_num) hcap
    have hmodExponent := thresholdDiffuse_second_modularExponent_ge
      hB hV hmargin hVupper
    have hmodTail := replay.secondTail hmodExponent
    have hmodTail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3) <
          (1 / 59 : ℝ) := by
      dsimp [s]
      convert hmodTail using 1
      all_goals ring_nf
    have henn : ENNReal.ofReal
          (∫ row, Real.exp
            (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
              Real.sqrt V) ^ 2)
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (97 / 200 : ℝ) := by
      calc
        _ ≤ ENNReal.ofReal
              (1 / Real.sqrt (1 + (99 / 25 : ℝ)) *
                (1 + 2 * Real.exp
                    (-((320 / 297 : ℝ) * (99 / 25) * Real.pi ^ 2 /
                      (2 * (1 + (99 / 25))))) /
                  (1 - (Real.exp
                    (-((320 / 297 : ℝ) * (99 / 25) * Real.pi ^ 2 /
                      (2 * (1 + (99 / 25)))))) ^ 3))) +
            ENNReal.ofReal
              (2 * Real.exp
                (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
                (1 - (Real.exp
                  (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) :=
            hcert
        _ ≤ ENNReal.ofReal (58 / 125 : ℝ) +
            ENNReal.ofReal (1 / 59 : ℝ) :=
          add_le_add
            (ENNReal.ofReal_mono replay.secondLobe.le)
            (ENNReal.ofReal_mono hmodTail'.le)
        _ = ENNReal.ofReal
            ((58 / 125 : ℝ) + (1 / 59 : ℝ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (97 / 200 : ℝ) := by
          exact ENNReal.ofReal_mono (by norm_num)
    simpa only [s] using
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 97 / 200)).mp henn

/-- Wrapped-Gaussian counterpart of the high-mass compact row theorem.  This
is the form stable under positive-Fourier coordinate deletion. -/
theorem sparseRow_diffuse_highMass_wrapped_le_97_div_200
    (replay : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128)
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (B V : ℝ)
    (hq : Odd q) (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hmargin : 3 * B ≤ (q : ℝ))
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : (11 / 10 : ℝ) * B ^ 2 ≤ V)
    (hVupper : V ≤ (25 / 16 : ℝ) * B ^ 2) :
    ∫ row, wrappedGaussianKernel q ((33 / 10 : ℝ) / B ^ 2)
        (∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure ≤
      97 / 200 := by
  let s : ℝ := (33 / 10 : ℝ) * V / B ^ 2
  have hs_pos : 0 < s := by dsimp [s]; positivity
  have hcap : ∀ i, (320 / 297 : ℝ) * s * (w i : ℝ) ^ 2 ≤ 2 * V := by
    intro i
    have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
    rw [show (320 / 297 : ℝ) * s * (w i : ℝ) ^ 2 =
      ((320 / 297 : ℝ) * (33 / 10) * V * (w i : ℝ) ^ 2) /
        B ^ 2 by dsimp [s]; ring]
    apply (div_le_iff₀ hBsq).2
    have hmul := mul_le_mul_of_nonneg_left (hdiffuse i) hV.le
    nlinarith
  have hperiod := sparseRow_wrappedGaussianKernel_normalized_nonzeroImageBound
    w q V s hq.pos hV h_norm hs_pos
  have hkernel : s / V = (33 / 10 : ℝ) / B ^ 2 := by
    dsimp [s]
    field_simp [hV.ne']
  rw [hkernel] at hperiod
  by_cases hfirst : V ≤ (6 / 5 : ℝ) * B ^ 2
  · have hsLower : (363 / 100 : ℝ) ≤ s := by
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      dsimp [s]
      apply (le_div_iff₀ hBsq).2
      nlinarith
    have hzero := sparseRow_normalized_nonmodulated_le_lobe_of_tilt_ratio
      w V hV h_norm (s := s) (sLower := (363 / 100 : ℝ))
        (r := (320 / 297 : ℝ)) (by norm_num) hsLower (by norm_num) hcap
    have hmodExponent := thresholdDiffuse_first_modularExponent_ge
      hB hV hmargin hfirst
    have hmodTail := replay.firstTail hmodExponent
    have hmodTail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3) <
          (1 / 198 : ℝ) := by
      dsimp [s]
      convert hmodTail using 1
      all_goals ring_nf
    have henn : ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q ((33 / 10 : ℝ) / B ^ 2)
            (∑ i, row i * w i) ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (97 / 200 : ℝ) := by
      calc
        _ ≤ ENNReal.ofReal
              (∫ row, Real.exp
                (-s * (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V) ^ 2)
                ∂(sparseRademacherRow d).toMeasure) +
            ENNReal.ofReal
              (2 * Real.exp
                (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
                (1 - (Real.exp
                  (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := hperiod
        _ ≤ ENNReal.ofReal (2399 / 5000 : ℝ) +
            ENNReal.ofReal (1 / 198 : ℝ) :=
          add_le_add
            (hzero.trans (ENNReal.ofReal_mono replay.firstLobe.le))
            (ENNReal.ofReal_mono hmodTail'.le)
        _ = ENNReal.ofReal ((2399 / 5000 : ℝ) + (1 / 198 : ℝ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (97 / 200 : ℝ) :=
          ENNReal.ofReal_mono (by norm_num)
    exact (ENNReal.ofReal_le_ofReal_iff
      (by norm_num : (0 : ℝ) ≤ 97 / 200)).mp henn
  · have hsecond : (6 / 5 : ℝ) * B ^ 2 ≤ V := le_of_not_ge hfirst
    have hsLower : (99 / 25 : ℝ) ≤ s := by
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      dsimp [s]
      apply (le_div_iff₀ hBsq).2
      nlinarith
    have hzero := sparseRow_normalized_nonmodulated_le_lobe_of_tilt_ratio
      w V hV h_norm (s := s) (sLower := (99 / 25 : ℝ))
        (r := (320 / 297 : ℝ)) (by norm_num) hsLower (by norm_num) hcap
    have hmodExponent := thresholdDiffuse_second_modularExponent_ge
      hB hV hmargin hVupper
    have hmodTail := replay.secondTail hmodExponent
    have hmodTail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3) <
          (1 / 59 : ℝ) := by
      dsimp [s]
      convert hmodTail using 1
      all_goals ring_nf
    have henn : ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q ((33 / 10 : ℝ) / B ^ 2)
            (∑ i, row i * w i) ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (97 / 200 : ℝ) := by
      calc
        _ ≤ ENNReal.ofReal
              (∫ row, Real.exp
                (-s * (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V) ^ 2)
                ∂(sparseRademacherRow d).toMeasure) +
            ENNReal.ofReal
              (2 * Real.exp
                (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
                (1 - (Real.exp
                  (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := hperiod
        _ ≤ ENNReal.ofReal (58 / 125 : ℝ) +
            ENNReal.ofReal (1 / 59 : ℝ) :=
          add_le_add
            (hzero.trans (ENNReal.ofReal_mono replay.secondLobe.le))
            (ENNReal.ofReal_mono hmodTail'.le)
        _ = ENNReal.ofReal ((58 / 125 : ℝ) + (1 / 59 : ℝ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (97 / 200 : ℝ) :=
          ENNReal.ofReal_mono (by norm_num)
    exact (ENNReal.ofReal_le_ofReal_iff
      (by norm_num : (0 : ℝ) ≤ 97 / 200)).mp henn

end CertifiedJL
