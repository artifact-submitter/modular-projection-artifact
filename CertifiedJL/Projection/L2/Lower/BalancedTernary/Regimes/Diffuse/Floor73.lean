/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Soundness.ThresholdBits128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.High
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Low
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedProfiles

/-! # Diffuse row bound for the floor-73 profile

This module proves the target-specific `539/1000` row cap at tilt `5/2`.
The compact profile is split at normalized masses `101/100`, `26/25`,
`11/10`, and `6/5`; the public support-selection and Fourier-deletion layers
remain target-neutral.
-/

open scoped BigOperators ENNReal
open MeasureTheory


namespace CertifiedJL
namespace ThresholdDiffuseFloor73

private theorem normalized_modularExponent_eq
    {B Q V : ℝ} (hB : 0 < B) (hV : 0 < V) :
    ((5 / 2 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (5 / 2 : ℝ) * V / B ^ 2) =
      (5 / 2 : ℝ) * Q ^ 2 / (B ^ 2 + (5 / 2 : ℝ) * V) := by
  have hsqrt : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  field_simp [hB.ne', hsqrt_ne]
  rw [hsqrt]
  field_simp [hV.ne']

private theorem modularExponent_ge
    {B Q V xCap c : ℝ} (hB : 0 < B) (hV : 0 < V)
    (hQ : 3 * B ≤ Q) (hVupper : V ≤ xCap * B ^ 2) (hc0 : 0 ≤ c)
    (hc : c * (1 + (5 / 2 : ℝ) * xCap) ≤ 45 / 2) :
    c ≤ ((5 / 2 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (5 / 2 : ℝ) * V / B ^ 2) := by
  rw [normalized_modularExponent_eq hB hV]
  have hQ2 : 9 * B ^ 2 ≤ Q ^ 2 := by
    nlinarith [sq_nonneg (Q - 3 * B)]
  have hden : 0 < B ^ 2 + (5 / 2 : ℝ) * V := by positivity
  apply (le_div_iff₀ hden).2
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  calc
    c * (B ^ 2 + (5 / 2 : ℝ) * V) ≤
        c * (B ^ 2 + (5 / 2 : ℝ) * (xCap * B ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hc0
      nlinarith
    _ = (c * (1 + (5 / 2 : ℝ) * xCap)) * B ^ 2 := by ring
    _ ≤ (45 / 2 : ℝ) * B ^ 2 := mul_le_mul_of_nonneg_right hc hBsq.le
    _ = (5 / 2 : ℝ) * (9 * B ^ 2) := by ring
    _ ≤ (5 / 2 : ℝ) * Q ^ 2 :=
      mul_le_mul_of_nonneg_left hQ2 (by norm_num)

private theorem sparseRow_nonmodulated_le
    {d : ℕ} (a : Fin d → ℝ) (S : Finset (Fin d))
    (hS : ∀ i, i ∈ S ↔ a i ≠ 0) (ha : ∑ i, a i ^ 2 = 1)
    {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hscalar : ∀ i, i ∈ S → sparseScalarF s (2 / a i ^ 2) ≤ C) :
    ENNReal.ofReal
        (∫ row, Real.exp (-s * realRowDot row a ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤ ENNReal.ofReal C := by
  have hreduce := sparseScalarReduction s a S hS hs ha
  refine hreduce.trans ?_
  calc
    _ ≤ ∏ i ∈ S, ENNReal.ofReal C ^ (a i ^ 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hai : a i ≠ 0 := (hS i).1 hi
        have hp : 0 < 2 / a i ^ 2 := by positivity
        have hm : gaussianCosineMoment s (2 / a i ^ 2) ≤ ENNReal.ofReal C := by
          rw [gaussianCosineMoment_eq_ofReal_sparseScalarF hp]
          exact ENNReal.ofReal_mono (hscalar i hi)
        exact ENNReal.rpow_le_rpow hm (sq_nonneg (a i))
    _ = ENNReal.ofReal (∏ i ∈ S, C ^ (a i ^ 2)) := by
      simp_rw [ENNReal.ofReal_rpow_of_nonneg hC (sq_nonneg (a _))]
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro i hi
      positivity
    _ = ENNReal.ofReal C := by
      congr 1
      rw [← Real.rpow_sum_of_nonneg hC (fun i hi => sq_nonneg (a i))]
      have hsum : ∑ i ∈ S, a i ^ 2 = 1 := by
        calc
          _ = ∑ i, a i ^ 2 := by
            apply Finset.sum_subset (by simp)
            intro i hi hnot
            have hai : a i = 0 := by
              by_contra h
              exact hnot ((hS i).2 h)
            simp [hai]
          _ = 1 := ha
      rw [hsum, Real.rpow_one]

private theorem low_nonmodulated_le
    {d : ℕ} (w : Fin d → ℤ) (B V C : ℝ)
    (hB : 0 < B) (hV : 0 < V) (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hscalar : ∀ {x p : ℝ}, x = V / B ^ 2 →
      (32 / 9) * x ≤ p → sparseScalarF ((5 / 2) * x) p < C)
    (hC : 0 ≤ C) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-((5 / 2 : ℝ) * V / B ^ 2) *
            (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤ ENNReal.ofReal C := by
  let x : ℝ := V / B ^ 2
  let s : ℝ := (5 / 2) * x
  let a : Fin d → ℝ := fun i => (w i : ℝ) / Real.sqrt V
  let S : Finset (Fin d) := Finset.univ.filter fun i => a i ≠ 0
  have hs : 0 ≤ s := by dsimp [s, x]; positivity
  have hsqrtSq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hS : ∀ i, i ∈ S ↔ a i ≠ 0 := by intro i; simp [S]
  have ha : ∑ i, a i ^ 2 = 1 := by
    calc
      _ = ∑ i, (w i : ℝ) ^ 2 / V := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [a]
        rw [div_pow, hsqrtSq]
      _ = (∑ i, (w i : ℝ) ^ 2) / V := by rw [Finset.sum_div]
      _ = V / V := by rw [h_norm]
      _ = 1 := div_self hV.ne'
  have hdot (row : Fin d → ℤ) :
      realRowDot row a =
        ((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V := by
    simp only [realRowDot, a, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hscalar' (i : Fin d) (hi : i ∈ S) :
      sparseScalarF s (2 / a i ^ 2) ≤ C := by
    have hai : a i ≠ 0 := (hS i).1 hi
    have hai2 : 0 < a i ^ 2 := sq_pos_of_ne_zero hai
    have hp : (32 / 9 : ℝ) * x ≤ 2 / a i ^ 2 := by
      apply (le_div_iff₀ hai2).2
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      have hid : ((32 / 9 : ℝ) * x) * a i ^ 2 =
          (32 / 9 : ℝ) * (w i : ℝ) ^ 2 / B ^ 2 := by
        dsimp [x, a]
        rw [div_pow, hsqrtSq]
        field_simp [hB.ne', hV.ne']
      rw [hid]
      apply (div_le_iff₀ hBsq).2
      nlinarith [hdiffuse i]
    exact (hscalar rfl hp).le
  have hzero := sparseRow_nonmodulated_le a S hS ha hs hC hscalar'
  simpa only [s, x, hdot, mul_div_assoc] using hzero

private theorem wrapped_low_le
    (replay : CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints)
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (B V : ℝ)
    (hq : Odd q) (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V) (hmargin : 3 * B ≤ (q : ℝ))
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : B ^ 2 ≤ V) (hVupper : V ≤ (11 / 10 : ℝ) * B ^ 2) :
    ∫ row, wrappedGaussianKernel q ((5 / 2 : ℝ) / B ^ 2)
        (∑ i, row i * w i) ∂(sparseRademacherRow d).toMeasure ≤ 539 / 1000 := by
  let s : ℝ := (5 / 2 : ℝ) * V / B ^ 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hperiod := sparseRow_wrappedGaussianKernel_normalized_nonzeroImageBound
    w q V s hq.pos hV h_norm hs
  have hkernel : s / V = (5 / 2 : ℝ) / B ^ 2 := by
    dsimp [s]
    field_simp [hV.ne']
  rw [hkernel] at hperiod
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  by_cases hfirst : V ≤ (101 / 100 : ℝ) * B ^ 2
  · have hx0 : 1 ≤ V / B ^ 2 := by
      apply (le_div_iff₀ hBsq).2
      simpa using hVlower
    have hx1 : V / B ^ 2 ≤ 101 / 100 := (div_le_iff₀ hBsq).2 hfirst
    have hzero := low_nonmodulated_le w B V (107 / 200) hB hV h_norm hdiffuse
      (fun hx hp => replay.lowScalarFirst (hx ▸ hx0) (hx ▸ hx1) (hx ▸ hp)) (by norm_num)
    have hexp := modularExponent_ge hB hV hmargin hfirst
      (xCap := (101 / 100 : ℝ)) (c := (300 / 47 : ℝ))
      (by norm_num) (by norm_num)
    have htail := replay.lowTailFirst hexp
    have htail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) ^ 3) <
          (7 / 2000 : ℝ) := by
      dsimp [s]
      convert htail using 1 <;> ring_nf
    have henn : ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q ((5 / 2 : ℝ) / B ^ 2)
            (∑ i, row i * w i) ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (539 / 1000 : ℝ) := by
      calc
        _ ≤ ENNReal.ofReal
              (∫ row, Real.exp
                (-s * (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V) ^ 2)
                ∂(sparseRademacherRow d).toMeasure) +
            ENNReal.ofReal
              (2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
                (1 - Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) ^ 3)) :=
          hperiod
        _ ≤ ENNReal.ofReal (107 / 200 : ℝ) + ENNReal.ofReal (7 / 2000 : ℝ) :=
          add_le_add hzero (ENNReal.ofReal_mono htail'.le)
        _ = ENNReal.ofReal ((107 / 200 : ℝ) + 7 / 2000) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (539 / 1000 : ℝ) := ENNReal.ofReal_mono (by norm_num)
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 539 / 1000)).mp henn
  · have hfirst' : (101 / 100 : ℝ) * B ^ 2 ≤ V := le_of_not_ge hfirst
    by_cases hsecond : V ≤ (26 / 25 : ℝ) * B ^ 2
    · have hx0 : (101 / 100 : ℝ) ≤ V / B ^ 2 :=
        (le_div_iff₀ hBsq).2 hfirst'
      have hx1 : V / B ^ 2 ≤ 26 / 25 := (div_le_iff₀ hBsq).2 hsecond
      have hzero := low_nonmodulated_le w B V (107 / 200) hB hV h_norm hdiffuse
        (fun hx hp => replay.lowScalarSecond (hx ▸ hx0) (hx ▸ hx1) (hx ▸ hp))
        (by norm_num)
      have hexp := modularExponent_ge hB hV hmargin hsecond
        (xCap := (26 / 25 : ℝ)) (c := (25 / 4 : ℝ))
        (by norm_num) (by norm_num)
      have htail := replay.lowTailSecond hexp
      have htail' :
          2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
              (1 - Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) ^ 3) <
            (1 / 250 : ℝ) := by
        dsimp [s]
        convert htail using 1 <;> ring_nf
      have henn := hperiod.trans (add_le_add hzero (ENNReal.ofReal_mono htail'.le))
      have hsum : ENNReal.ofReal (107 / 200 : ℝ) + ENNReal.ofReal (1 / 250 : ℝ) =
          ENNReal.ofReal (539 / 1000 : ℝ) := by
        calc
          _ = ENNReal.ofReal ((107 / 200 : ℝ) + 1 / 250) := by
            rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
          _ = _ := by norm_num
      rw [hsum] at henn
      exact (ENNReal.ofReal_le_ofReal_iff
        (by norm_num : (0 : ℝ) ≤ 539 / 1000)).mp henn
    · have hsecond' : (26 / 25 : ℝ) * B ^ 2 ≤ V := le_of_not_ge hsecond
      have hx0 : (26 / 25 : ℝ) ≤ V / B ^ 2 := (le_div_iff₀ hBsq).2 hsecond'
      have hx1 : V / B ^ 2 ≤ 11 / 10 := (div_le_iff₀ hBsq).2 hVupper
      have hzero := low_nonmodulated_le w B V (267 / 500) hB hV h_norm hdiffuse
        (fun hx hp => replay.lowScalarThird (hx ▸ hx0) (hx ▸ hx1) (hx ▸ hp))
        (by norm_num)
      have hexp := modularExponent_ge hB hV hmargin hVupper
        (xCap := (11 / 10 : ℝ)) (c := (6 : ℝ))
        (by norm_num) (by norm_num)
      have htail := replay.lowTailThird hexp
      have htail' :
          2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
              (1 - Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) ^ 3) <
            (1 / 200 : ℝ) := by
        dsimp [s]
        convert htail using 1 <;> ring_nf
      have henn := hperiod.trans (add_le_add hzero (ENNReal.ofReal_mono htail'.le))
      have hsum : ENNReal.ofReal (267 / 500 : ℝ) + ENNReal.ofReal (1 / 200 : ℝ) =
          ENNReal.ofReal (539 / 1000 : ℝ) := by
        calc
          _ = ENNReal.ofReal ((267 / 500 : ℝ) + 1 / 200) := by
            rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
          _ = _ := by norm_num
      rw [hsum] at henn
      exact (ENNReal.ofReal_le_ofReal_iff
        (by norm_num : (0 : ℝ) ≤ 539 / 1000)).mp henn

private theorem wrapped_high_le
    (replay : CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints)
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (B V : ℝ)
    (hq : Odd q) (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V) (hmargin : 3 * B ≤ (q : ℝ))
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : (11 / 10 : ℝ) * B ^ 2 ≤ V)
    (hVupper : V ≤ (25 / 16 : ℝ) * B ^ 2) :
    ∫ row, wrappedGaussianKernel q ((5 / 2 : ℝ) / B ^ 2)
        (∑ i, row i * w i) ∂(sparseRademacherRow d).toMeasure ≤ 539 / 1000 := by
  let s : ℝ := (5 / 2 : ℝ) * V / B ^ 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hcap : ∀ i, (64 / 45 : ℝ) * s * (w i : ℝ) ^ 2 ≤ 2 * V := by
    intro i
    have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
    rw [show (64 / 45 : ℝ) * s * (w i : ℝ) ^ 2 =
      ((32 / 9 : ℝ) * V * (w i : ℝ) ^ 2) / B ^ 2 by dsimp [s]; ring]
    apply (div_le_iff₀ hBsq).2
    have hmul := mul_le_mul_of_nonneg_left (hdiffuse i) hV.le
    nlinarith
  have hperiod := sparseRow_wrappedGaussianKernel_normalized_nonzeroImageBound
    w q V s hq.pos hV h_norm hs
  have hkernel : s / V = (5 / 2 : ℝ) / B ^ 2 := by
    dsimp [s]
    field_simp [hV.ne']
  rw [hkernel] at hperiod
  by_cases hfirst : V ≤ (6 / 5 : ℝ) * B ^ 2
  · have hsLower : (11 / 4 : ℝ) ≤ s := by
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      dsimp [s]
      apply (le_div_iff₀ hBsq).2
      nlinarith
    have hzero := sparseRow_normalized_nonmodulated_le_lobe_of_tilt_ratio
      w V hV h_norm (s := s) (sLower := (11 / 4 : ℝ))
        (r := (64 / 45 : ℝ)) (by norm_num) hsLower (by norm_num) hcap
    have hexp := modularExponent_ge hB hV hmargin hfirst
      (xCap := (6 / 5 : ℝ)) (c := (45 / 8 : ℝ))
      (by norm_num) (by norm_num)
    have htail := replay.highFirstTail hexp
    have htail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) ^ 3) <
          (3 / 400 : ℝ) := by
      dsimp [s]
      convert htail using 1 <;> ring_nf
    have henn := hperiod.trans (add_le_add
      (hzero.trans (ENNReal.ofReal_mono replay.highFirstLobe.le))
      (ENNReal.ofReal_mono htail'.le))
    have hsum : ENNReal.ofReal (523 / 1000 : ℝ) + ENNReal.ofReal (3 / 400 : ℝ) ≤
        ENNReal.ofReal (539 / 1000 : ℝ) := by
      calc
        _ = ENNReal.ofReal ((523 / 1000 : ℝ) + 3 / 400) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ _ := ENNReal.ofReal_mono (by norm_num)
    exact (ENNReal.ofReal_le_ofReal_iff
      (by norm_num : (0 : ℝ) ≤ 539 / 1000)).mp (henn.trans hsum)
  · have hsecond : (6 / 5 : ℝ) * B ^ 2 ≤ V := le_of_not_ge hfirst
    have hsLower : (3 : ℝ) ≤ s := by
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      dsimp [s]
      apply (le_div_iff₀ hBsq).2
      nlinarith
    have hzero := sparseRow_normalized_nonmodulated_le_lobe_of_tilt_ratio
      w V hV h_norm (s := s) (sLower := (3 : ℝ))
        (r := (64 / 45 : ℝ)) (by norm_num) hsLower (by norm_num) hcap
    have hexp := modularExponent_ge hB hV hmargin hVupper
      (xCap := (25 / 16 : ℝ)) (c := (720 / 157 : ℝ))
      (by norm_num) (by norm_num)
    have htail := replay.highSecondTail hexp
    have htail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) ^ 3) <
          (21 / 1000 : ℝ) := by
      dsimp [s]
      convert htail using 1 <;> ring_nf
    have henn := hperiod.trans (add_le_add
      (hzero.trans (ENNReal.ofReal_mono replay.highSecondLobe.le))
      (ENNReal.ofReal_mono htail'.le))
    have hsum : ENNReal.ofReal (253 / 500 : ℝ) + ENNReal.ofReal (21 / 1000 : ℝ) ≤
        ENNReal.ofReal (539 / 1000 : ℝ) := by
      calc
        _ = ENNReal.ofReal ((253 / 500 : ℝ) + 21 / 1000) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ _ := ENNReal.ofReal_mono (by norm_num)
    exact (ENNReal.ofReal_le_ofReal_iff
      (by norm_num : (0 : ℝ) ≤ 539 / 1000)).mp (henn.trans hsum)

/-- Public compact wrapped estimate at tilt `5/2`, before centered transport. -/
theorem sparseRow_diffuseCompact_wrapped_le_539_div_1000
    (replay : CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints)
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (B V : ℝ)
    (hq : Odd q) (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V) (hmargin : 3 * B ≤ (q : ℝ))
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : B ^ 2 ≤ V) (hVupper : V ≤ (25 / 16 : ℝ) * B ^ 2) :
    ∫ row, wrappedGaussianKernel q ((5 / 2 : ℝ) / B ^ 2)
        (∑ i, row i * w i) ∂(sparseRademacherRow d).toMeasure ≤ 539 / 1000 := by
  by_cases hlow : V ≤ (11 / 10 : ℝ) * B ^ 2
  · exact wrapped_low_le replay w q B V hq hB hV h_norm hmargin hdiffuse hVlower hlow
  · exact wrapped_high_le replay w q B V hq hB hV h_norm hmargin hdiffuse
      (le_of_not_ge hlow) hVupper

/-- Retained wrapped diffuse bound at tilt `5/2`, shared by affine and centered tails. -/
theorem wrappedRowBound_marginThree_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints) :
    SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000) := by
  intro q d w inputThreshold hq hpositive hnorm hmarginNat hdiffuse
  obtain ⟨support, hlower, hupper⟩ :=
    exists_threshold_subprofile_of_three_quarters
      w inputThreshold hpositive hnorm hdiffuse
  let v : Fin d → ℤ := fun i => if i ∈ support then w i else 0
  let B : ℝ := inputThreshold
  let V : ℝ := sqNorm v
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast hpositive
  have hVlower : B ^ 2 ≤ V := by
    dsimp [B, V]
    exact_mod_cast hlower
  have hV : 0 < V := lt_of_lt_of_le (sq_pos_of_pos hB) hVlower
  have hVupper : V ≤ (25 / 16 : ℝ) * B ^ 2 := by
    have hupper' : 16 * V < 25 * B ^ 2 := by
      dsimp [B, V]
      exact_mod_cast hupper
    nlinarith
  have h_norm : ∑ i, (v i : ℝ) ^ 2 = V := (realCast_sqNorm v).symm
  have hmargin : 3 * B ≤ (q : ℝ) := by
    dsimp [B]
    exact_mod_cast hmarginNat
  have hdiffuseReal : ∀ i, 16 * (v i : ℝ) ^ 2 ≤ 9 * B ^ 2 := by
    intro i
    by_cases hi : i ∈ support
    · have hsquare := Nat.pow_le_pow_left (hdiffuse i) 2
      have hnat : 16 * (w i).natAbs ^ 2 ≤ 9 * inputThreshold ^ 2 := by
        simpa [mul_pow] using hsquare
      have hnatReal : (16 : ℝ) * ((w i).natAbs : ℝ) ^ 2 ≤
          9 * (inputThreshold : ℝ) ^ 2 := by exact_mod_cast hnat
      dsimp [v, B]
      simp only [if_pos hi]
      have habs : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [habs, sq_abs] at hnatReal
      exact hnatReal
    · simp [v, hi, sq_nonneg B]
  exact ⟨support, sparseRow_diffuseCompact_wrapped_le_539_div_1000
    replay v q B V hq hB hV h_norm hmargin hdiffuseReal hVlower hVupper⟩

/-- The original centered row provider follows from the shared wrapped estimate. -/
theorem rowBound_marginThree_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints) :
    SparseThresholdDiffuseRowBoundWithAt (5 / 2) (539 / 1000)
      (NonnegativeRatio.ofNat 3) := by
  intro q d w b hq _hcentered hpositive hnorm hmodulus hdiffuse
  have hmargin : 3 * b ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmodulus
  obtain ⟨support, hwrapped⟩ :=
    wrappedRowBound_marginThree_of_replay replay q d w b hq hpositive hnorm hmargin hdiffuse
  exact (sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict w support hq
    (by positivity : 0 < (5 / 2 : ℝ) / (b : ℝ) ^ 2)).trans hwrapped

end ThresholdDiffuseFloor73
end CertifiedJL
