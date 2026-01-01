/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.CosineLaplace
import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier

/-!
# Low-mass diffuse threshold rows

The scalar certificate is tensorized here over a normalized balanced-ternary
row.  The theorem deliberately isolates the zero modular image: the complete
wrapped-image contribution needs a coupled diffuse estimate, since the generic
subgaussian image tail is not sharp enough at the endpoint `V = B²`.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
namespace ThresholdDiffuseLow

private theorem sparseRow_nonmodulated_le_of_scalar_cap
    {d : ℕ} (a : Fin d → ℝ) (S : Finset (Fin d))
    (hS : ∀ i, i ∈ S ↔ a i ≠ 0)
    (ha : ∑ i, a i ^ 2 = 1) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hscalar : ∀ i, i ∈ S → sparseScalarF s (2 / (a i ^ 2)) ≤ C) :
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal C := by
  have hreduce := sparseScalarReduction s a S hS hs ha
  refine hreduce.trans ?_
  calc
    (∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2)) ≤
        ∏ i ∈ S, ENNReal.ofReal C ^ (a i ^ 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hai : a i ≠ 0 := (hS i).1 hi
        have hp_pos : 0 < 2 / (a i ^ 2) := by positivity
        have hmoment : gaussianCosineMoment s (2 / (a i ^ 2)) ≤
            ENNReal.ofReal C := by
          rw [gaussianCosineMoment_eq_ofReal_sparseScalarF hp_pos]
          exact ENNReal.ofReal_mono (hscalar i hi)
        exact ENNReal.rpow_le_rpow hmoment (sq_nonneg (a i))
    _ = ENNReal.ofReal (∏ i ∈ S, C ^ (a i ^ 2)) := by
      simp_rw [ENNReal.ofReal_rpow_of_nonneg hC (sq_nonneg (a _))]
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro i hi
      positivity
    _ = ENNReal.ofReal C := by
      congr 1
      rw [← Real.rpow_sum_of_nonneg hC (fun i hi ↦ sq_nonneg (a i))]
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

/-- The full low-mass zero-image estimate.  It is uniform in the number and
sizes of coordinates, and uses only the public diffuse coordinate cap. -/
theorem sparseRow_diffuse_lowMass_nonmodulated_le
    (replay : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    {d : ℕ} (w : Fin d → ℤ) (B V : ℝ)
    (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : B ^ 2 ≤ V)
    (hVupper : V ≤ (11 / 10 : ℝ) * B ^ 2) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-((33 / 10 : ℝ) * V / B ^ 2) *
            (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal (603 / 1250 : ℝ) := by
  let x : ℝ := V / B ^ 2
  let s : ℝ := (33 / 10) * x
  let a : Fin d → ℝ := fun i ↦ (w i : ℝ) / Real.sqrt V
  let S : Finset (Fin d) := Finset.univ.filter fun i ↦ a i ≠ 0
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hx0 : 1 ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hBsq).2 (by simpa using hVlower)
  have hx1 : x ≤ 11 / 10 := by
    dsimp [x]
    exact (div_le_iff₀ hBsq).2 (by simpa [mul_comm] using hVupper)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hsqrt_sq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
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
  have hreduce := sparseScalarReduction s a S hS hs0 ha
  have hscalar (i : Fin d) (hi : i ∈ S) :
      sparseScalarF s (2 / (a i ^ 2)) < (603 / 1250 : ℝ) := by
    have hai : a i ≠ 0 := (hS i).1 hi
    have hai2 : 0 < a i ^ 2 := sq_pos_of_ne_zero hai
    have hp : (32 / 9 : ℝ) * x ≤ 2 / (a i ^ 2) := by
      apply (le_div_iff₀ hai2).2
      have hid :
          ((32 / 9 : ℝ) * x) * a i ^ 2 =
            (32 / 9 : ℝ) * (w i : ℝ) ^ 2 / B ^ 2 := by
        dsimp [x, a]
        rw [div_pow, hsqrt_sq]
        field_simp [hB.ne', hV.ne']
      rw [hid]
      apply (div_le_iff₀ hBsq).2
      nlinarith [hdiffuse i]
    by_cases hxsplit : x ≤ 26 / 25
    · exact replay.lowBand hx0 hxsplit hp
    · have hxsplit' : (26 / 25 : ℝ) ≤ x := le_of_not_ge hxsplit
      exact (replay.highBand
        hxsplit' hx1 hp).trans_le (by norm_num)
  have hprod :
      (∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2)) ≤
        ENNReal.ofReal (603 / 1250 : ℝ) := by
    calc
      (∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2)) ≤
          ∏ i ∈ S, ENNReal.ofReal (603 / 1250 : ℝ) ^ (a i ^ 2) := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          have hai : a i ≠ 0 := (hS i).1 hi
          have hp_pos : 0 < 2 / (a i ^ 2) := by positivity
          have hmoment : gaussianCosineMoment s (2 / (a i ^ 2)) ≤
              ENNReal.ofReal (603 / 1250 : ℝ) := by
            rw [gaussianCosineMoment_eq_ofReal_sparseScalarF hp_pos]
            exact ENNReal.ofReal_mono (hscalar i hi).le
          exact ENNReal.rpow_le_rpow hmoment (sq_nonneg (a i))
      _ = ENNReal.ofReal
          (∏ i ∈ S, (603 / 1250 : ℝ) ^ (a i ^ 2)) := by
        simp_rw [ENNReal.ofReal_rpow_of_nonneg
          (by norm_num : (0 : ℝ) ≤ 603 / 1250) (sq_nonneg (a _))]
        rw [ENNReal.ofReal_prod_of_nonneg]
        intro i hi
        positivity
      _ = ENNReal.ofReal (603 / 1250 : ℝ) := by
        congr 1
        rw [← Real.rpow_sum_of_nonneg
          (by norm_num : (0 : ℝ) ≤ 603 / 1250)
          (fun i hi ↦ sq_nonneg (a i))]
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
  have hzero := hreduce.trans hprod
  simpa only [s, x, hdot, mul_div_assoc] using hzero

/-- The stronger zero-image cap on the upper half of the low-mass band. -/
theorem sparseRow_diffuse_upperLowMass_nonmodulated_le
    (replay : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    {d : ℕ} (w : Fin d → ℤ) (B V : ℝ)
    (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : (26 / 25 : ℝ) * B ^ 2 ≤ V)
    (hVupper : V ≤ (11 / 10 : ℝ) * B ^ 2) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-((33 / 10 : ℝ) * V / B ^ 2) *
            (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal (12 / 25 : ℝ) := by
  let x : ℝ := V / B ^ 2
  let s : ℝ := (33 / 10) * x
  let a : Fin d → ℝ := fun i ↦ (w i : ℝ) / Real.sqrt V
  let S : Finset (Fin d) := Finset.univ.filter fun i ↦ a i ≠ 0
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hx0 : (26 / 25 : ℝ) ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hBsq).2 (by simpa [mul_comm] using hVlower)
  have hx1 : x ≤ 11 / 10 := by
    dsimp [x]
    exact (div_le_iff₀ hBsq).2 (by simpa [mul_comm] using hVupper)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
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
  have hdot (row : Fin d → ℤ) :
      realRowDot row a =
        ((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V := by
    simp only [realRowDot, a, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hscalar (i : Fin d) (hi : i ∈ S) :
      sparseScalarF s (2 / (a i ^ 2)) ≤ (12 / 25 : ℝ) := by
    have hai : a i ≠ 0 := (hS i).1 hi
    have hai2 : 0 < a i ^ 2 := sq_pos_of_ne_zero hai
    have hp : (32 / 9 : ℝ) * x ≤ 2 / (a i ^ 2) := by
      apply (le_div_iff₀ hai2).2
      have hid :
          ((32 / 9 : ℝ) * x) * a i ^ 2 =
            (32 / 9 : ℝ) * (w i : ℝ) ^ 2 / B ^ 2 := by
        dsimp [x, a]
        rw [div_pow, hsqrt_sq]
        field_simp [hB.ne', hV.ne']
      rw [hid]
      apply (div_le_iff₀ hBsq).2
      nlinarith [hdiffuse i]
    exact (replay.highBand
      hx0 hx1 hp).le
  have hzero := sparseRow_nonmodulated_le_of_scalar_cap
    a S hS ha hs0 (by norm_num : (0 : ℝ) ≤ 12 / 25) hscalar
  simpa only [s, x, hdot, mul_div_assoc] using hzero

private theorem normalized_modularExponent_eq
    {B Q V : ℝ} (hB : 0 < B) (hV : 0 < V) :
    ((33 / 10 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (33 / 10 : ℝ) * V / B ^ 2) =
      (33 / 10 : ℝ) * Q ^ 2 /
        (B ^ 2 + (33 / 10 : ℝ) * V) := by
  have hsqrt : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  field_simp [hB.ne', hsqrt_ne]
  rw [hsqrt]
  field_simp [hV.ne']

private theorem lowBand_modularExponent_ge
    {B Q V : ℝ} (hB : 0 < B) (hV : 0 < V)
    (hQ : 3 * B ≤ Q) (hVupper : V ≤ (26 / 25 : ℝ) * B ^ 2) :
    (7425 / 1108 : ℝ) ≤
      ((33 / 10 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (33 / 10 : ℝ) * V / B ^ 2) := by
  rw [normalized_modularExponent_eq hB hV]
  have hQ2 : 9 * B ^ 2 ≤ Q ^ 2 := by
    nlinarith [sq_nonneg (Q - 3 * B)]
  have hden : 0 < B ^ 2 + (33 / 10 : ℝ) * V := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem fullLowBand_modularExponent_ge
    {B Q V : ℝ} (hB : 0 < B) (hV : 0 < V)
    (hQ : 3 * B ≤ Q) (hVupper : V ≤ (11 / 10 : ℝ) * B ^ 2) :
    (2970 / 463 : ℝ) ≤
      ((33 / 10 : ℝ) * V / B ^ 2) * (Q / Real.sqrt V) ^ 2 /
        (1 + (33 / 10 : ℝ) * V / B ^ 2) := by
  rw [normalized_modularExponent_eq hB hV]
  have hQ2 : 9 * B ^ 2 ≤ Q ^ 2 := by
    nlinarith [sq_nonneg (Q - 3 * B)]
  have hden : 0 < B ^ 2 + (33 / 10 : ℝ) * V := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The wrapped compact row, which is the endpoint required by positive
Fourier deletion, is below the public `97/200` cap throughout `x∈[1,1.1]`.
The split at `26/25` preserves the coupling between scalar and image slack. -/
theorem sparseRow_diffuse_lowMass_wrapped_le_97_div_200
    (scalarReplay : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (tailReplay : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (B V : ℝ)
    (hq : Odd q) (hB : 0 < B) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hmargin : 3 * B ≤ (q : ℝ))
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : B ^ 2 ≤ V)
    (hVupper : V ≤ (11 / 10 : ℝ) * B ^ 2) :
    ∫ row, wrappedGaussianKernel q ((33 / 10 : ℝ) / B ^ 2)
        (∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure ≤
      97 / 200 := by
  let s : ℝ := (33 / 10 : ℝ) * V / B ^ 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hperiod := sparseRow_wrappedGaussianKernel_normalized_nonzeroImageBound
    w q V s hq.pos hV h_norm hs
  have hkernel : s / V = (33 / 10 : ℝ) / B ^ 2 := by
    dsimp [s]
    field_simp [hV.ne']
  rw [hkernel] at hperiod
  by_cases hsplit : V ≤ (26 / 25 : ℝ) * B ^ 2
  · have hzero := sparseRow_diffuse_lowMass_nonmodulated_le scalarReplay
      w B V hB hV h_norm hdiffuse hVlower
      (hsplit.trans (by nlinarith [sq_nonneg B]))
    have hexponent := lowBand_modularExponent_ge hB hV hmargin hsplit
    have htail := tailReplay.lowBand hexponent
    have htail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3) <
          (13 / 5000 : ℝ) := by
      dsimp [s]
      convert htail using 1 <;> ring_nf
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
              (2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
                (1 - (Real.exp
                  (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := hperiod
        _ ≤ ENNReal.ofReal (603 / 1250 : ℝ) +
            ENNReal.ofReal (13 / 5000 : ℝ) :=
          add_le_add hzero (ENNReal.ofReal_mono htail'.le)
        _ = ENNReal.ofReal
            ((603 / 1250 : ℝ) + (13 / 5000 : ℝ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (97 / 200 : ℝ) :=
          ENNReal.ofReal_mono (by norm_num)
    exact (ENNReal.ofReal_le_ofReal_iff
      (by norm_num : (0 : ℝ) ≤ 97 / 200)).mp henn

  · have hsplit' : (26 / 25 : ℝ) * B ^ 2 ≤ V := le_of_not_ge hsplit
    have hzero := sparseRow_diffuse_upperLowMass_nonmodulated_le scalarReplay
      w B V hB hV h_norm hdiffuse hsplit' hVupper
    have hexponent := fullLowBand_modularExponent_ge hB hV hmargin hVupper
    have htail := tailReplay.fullBand hexponent
    have htail' :
        2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3) <
          (1 / 200 : ℝ) := by
      dsimp [s]
      convert htail using 1 <;> ring_nf
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
              (2 * Real.exp (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
                (1 - (Real.exp
                  (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := hperiod
        _ ≤ ENNReal.ofReal (12 / 25 : ℝ) +
            ENNReal.ofReal (1 / 200 : ℝ) :=
          add_le_add hzero (ENNReal.ofReal_mono htail'.le)
        _ = ENNReal.ofReal ((12 / 25 : ℝ) + (1 / 200 : ℝ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (97 / 200 : ℝ) :=
          ENNReal.ofReal_mono (by norm_num)
    exact (ENNReal.ofReal_le_ofReal_iff
      (by norm_num : (0 : ℝ) ≤ 97 / 200)).mp henn

/-- Full-profile low-mass transport.  Positive Fourier deletion first removes
every coordinate outside the supplied greedy support; the compact wrapped
certificate then closes the row. -/
theorem sparseRow_diffuse_lowMass_le_97_div_200_of_restrict
    (scalarReplay : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (tailReplay : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    {d : ℕ} (w : Fin d → ℤ) (support : Finset (Fin d))
    (q : ℕ) (B V : ℝ)
    (hq : Odd q) (hB : 0 < B) (hV : 0 < V)
    (h_norm :
      ∑ i, ((if i ∈ support then w i else 0 : ℤ) : ℝ) ^ 2 = V)
    (hmargin : 3 * B ≤ (q : ℝ))
    (hdiffuse : ∀ i, 16 * (w i : ℝ) ^ 2 ≤ 9 * B ^ 2)
    (hVlower : B ^ 2 ≤ V)
    (hVupper : V ≤ (11 / 10 : ℝ) * B ^ 2) :
    ∫ row, Real.exp
        (-((33 / 10 : ℝ) / B ^ 2) * sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      97 / 200 := by
  let v : Fin d → ℤ := fun i ↦ if i ∈ support then w i else 0
  have hs : 0 < (33 / 10 : ℝ) / B ^ 2 := by positivity
  have htransport := sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict
    w support hq hs
  have hdiffuse_v : ∀ i, 16 * (v i : ℝ) ^ 2 ≤ 9 * B ^ 2 := by
    intro i
    by_cases hi : i ∈ support
    · simpa [v, hi] using hdiffuse i
    · simp [v, hi, sq_nonneg B]
  have hcompact := sparseRow_diffuse_lowMass_wrapped_le_97_div_200
    scalarReplay tailReplay v q B V hq hB hV (by simpa [v] using h_norm) hmargin hdiffuse_v
      hVlower hVupper
  exact htransport.trans (by simpa [v] using hcompact)

end ThresholdDiffuseLow
end CertifiedJL
