/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.PMF
import CertifiedJL.Probability.Distributions.Rademacher.RademacherExactMoments
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwentyOneFiftiethMomentCorrection

/-!
# A degree-ten polynomial tail bound for normalized Rademacher sums

An exact nonnegative polynomial majorizes the squared tail event at the
threshold required by the sparse `21/50` endpoint.  Its expectation is bounded
using the exact moments through degree ten and an elementary power-sum
correction.  Every arithmetic certificate is checked by Lean's kernel.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL.SparseLInfLower21Over50

open Probability

noncomputable local instance (priority := 10000) twentyOneFiftiethTailDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

noncomputable def twentyOneFiftiethTailPolynomial (X : ℝ) : ℝ :=
  X * (X - 139 / 100) ^ 2 * ((X - 61 / 4) ^ 2 + 4)

lemma twentyOneFiftiethTailPolynomial_expanded (X : ℝ) :
    twentyOneFiftiethTailPolynomial X =
      (14625997 / 32000) * X - (447858 / 625) * X ^ 2 +
      (1616423 / 5000) * X ^ 3 - (832 / 25) * X ^ 4 + X ^ 5 := by
  unfold twentyOneFiftiethTailPolynomial
  ring

lemma twentyOneFiftiethTailPolynomial_nonneg {X : ℝ} (hX : 0 ≤ X) :
    0 ≤ twentyOneFiftiethTailPolynomial X := by
  unfold twentyOneFiftiethTailPolynomial
  positivity

noncomputable def twentyOneFiftiethTailDifferenceQuotient (y : ℝ) : ℝ :=
  366388468740885346778687368434090400801 /
      81920000000000000000000000000000000 +
    (6181874989537377130741790649 /
      51200000000000000000000000) * y -
    (7261947049002879599 / 64000000000000000) * y ^ 2 -
    (633508951 / 160000000) * y ^ 3 + y ^ 4

lemma twentyOneFiftiethTailPolynomial_sub_at_threshold (X : ℝ) :
    twentyOneFiftiethTailPolynomial X -
        twentyOneFiftiethTailPolynomial (4691291049 / 800000000) =
      (X - 4691291049 / 800000000) *
        twentyOneFiftiethTailDifferenceQuotient
          (X - 4691291049 / 800000000) := by
  unfold twentyOneFiftiethTailPolynomial twentyOneFiftiethTailDifferenceQuotient
  ring

set_option maxHeartbeats 1000000 in
lemma twentyOneFiftiethTailDifferenceQuotient_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ twentyOneFiftiethTailDifferenceQuotient y := by
  have hsos : twentyOneFiftiethTailDifferenceQuotient y =
      (y ^ 2 - (633508951 / 320000000 : ℝ) * y - 6343 / 100) ^ 2 +
      (4850075652991361203 / 512000000000000000 : ℝ) *
        (y - 6676836294280222869258209351 /
          970015130598272240600000000) ^ 2 +
      (135130249669138024777731562249808506190010773056158799 /
        397318197493052309749760000000000000000000000000000000 : ℝ) := by
    unfold twentyOneFiftiethTailDifferenceQuotient
    ring
  rw [hsos]
  positivity

theorem twentyOneFiftiethTailPolynomial_threshold_le {X : ℝ}
    (hX : (4691291049 / 800000000 : ℝ) ≤ X) :
    twentyOneFiftiethTailPolynomial (4691291049 / 800000000) ≤
      twentyOneFiftiethTailPolynomial X := by
  have hy : 0 ≤ X - (4691291049 / 800000000 : ℝ) := sub_nonneg.mpr hX
  have hq := twentyOneFiftiethTailDifferenceQuotient_nonneg hy
  rw [← sub_nonneg, twentyOneFiftiethTailPolynomial_sub_at_threshold]
  exact mul_nonneg hy hq

lemma twentyOneFiftiethTailPolynomial_threshold_pos :
    0 < twentyOneFiftiethTailPolynomial (4691291049 / 800000000) := by
  unfold twentyOneFiftiethTailPolynomial
  norm_num

set_option maxHeartbeats 2000000 in
theorem twentyOneFiftiethTailPolynomial_expect_le_gaussian
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (𝔼 bits : Fin n → Bool,
        twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2)) ≤
      97154081 / 160000 := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n)) (fun i => a i ^ 2) Finset.univ_nonempty
  let m : ℝ := a i ^ 2
  have hm_le : ∀ j, a j ^ 2 ≤ m := by
    intro j
    exact hi j (Finset.mem_univ j)
  have hm_eq : ∃ j, a j ^ 2 = m := ⟨i, rfl⟩
  have hcorr := twentyOneFiftiethMomentCorrection_nonpos (fun j => a j ^ 2) m
    (fun j => sq_nonneg (a j)) hm_le hm_eq ha
  have hpoly (bits : Fin n → Bool) :
      twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2) =
        (14625997 / 32000) * (rademacherSum a bits) ^ 2 -
        (447858 / 625) * (rademacherSum a bits) ^ 4 +
        (1616423 / 5000) * (rademacherSum a bits) ^ 6 -
        (832 / 25) * (rademacherSum a bits) ^ 8 +
        (rademacherSum a bits) ^ 10 := by
    rw [twentyOneFiftiethTailPolynomial_expanded]
    ring
  simp_rw [hpoly]
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect]
  change
    (14625997 / 32000) * radMoment a 2 -
      (447858 / 625) * radMoment a 4 +
      (1616423 / 5000) * radMoment a 6 -
      (832 / 25) * radMoment a 8 + radMoment a 10 ≤
        97154081 / 160000
  rw [radMoment_two_exact, radMoment_four_exact, radMoment_six_exact,
    radMoment_eight_exact, radMoment_ten_exact]
  have hP1 : coeffPowerSum a 1 = 1 := by
    simpa only [coeffPowerSum, pow_one] using ha
  rw [hP1]
  have hpower (k : ℕ) :
      powerSum (fun j => a j ^ 2) k = coeffPowerSum a k := by
    rfl
  rw [hpower 2, hpower 3, hpower 4, hpower 5] at hcorr
  unfold twentyOneFiftiethMomentCorrection at hcorr
  nlinarith

theorem integral_rademacher_eq_expect {n : ℕ}
    (f : (Fin n → Bool) → ℝ) :
    (∫ bits, f bits ∂(rademacherPMF (Fin n)).toMeasure) =
      𝔼 bits : Fin n → Bool, f bits := by
  classical
  rw [finitePMF_integral_eq_sum]
  simp only [rademacherPMF, uniformPiPMF_eq_uniformOfFintype,
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, Fintype.expect_eq_sum_div_card]
  rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]

theorem twentyOneFiftiethTailPolynomial_expect_le_gaussian_fintype
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (𝔼 bits : ι → Bool,
        twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2)) ≤
      97154081 / 160000 := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let a' : Fin (Fintype.card ι) → ℝ := fun i => a (e i)
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
  have ha' : ∑ i, a' i ^ 2 = 1 := by
    dsimp [a']
    rw [Equiv.sum_comp e (fun i => a i ^ 2)]
    exact ha
  have h := twentyOneFiftiethTailPolynomial_expect_le_gaussian hn a' ha'
  calc
    (𝔼 bits : ι → Bool,
        twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2)) =
      𝔼 bits : Fin (Fintype.card ι) → Bool,
        twentyOneFiftiethTailPolynomial ((rademacherSum a' bits) ^ 2) := by
        symm
        apply Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
        intro bits
        rw [rademacherSum_equiv]
    _ ≤ 97154081 / 160000 := h

theorem integral_rademacher_eq_expect_fintype
    {ι : Type*} [Fintype ι] (f : (ι → Bool) → ℝ) :
    (∫ bits, f bits ∂(rademacherPMF ι).toMeasure) =
      𝔼 bits : ι → Bool, f bits := by
  classical
  rw [finitePMF_integral_eq_sum]
  simp only [rademacherPMF, uniformPiPMF_eq_uniformOfFintype,
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, Fintype.expect_eq_sum_div_card]
  rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]

theorem rademacherSum_normalized_twentyOneFiftieth_tail_toReal_lt
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (eventProbability (rademacherPMF (Fin n))
      (fun bits => (4691291049 / 800000000 : ℝ) ≤
        (rademacherSum a bits) ^ 2)).toReal < 57 / 1000 := by
  classical
  let A : ℝ := 4691291049 / 800000000
  let event : (Fin n → Bool) → Prop := fun bits =>
    A ≤ (rademacherSum a bits) ^ 2
  let F : (Fin n → Bool) → ℝ := fun bits =>
    twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2) /
      twentyOneFiftiethTailPolynomial A
  have hpoint (bits : Fin n → Bool) :
      (if event bits then (1 : ℝ) else 0) ≤ F bits := by
    by_cases he : event bits
    · rw [if_pos he]
      dsimp only [F]
      apply (le_div_iff₀ (by
        dsimp only [A]
        exact twentyOneFiftiethTailPolynomial_threshold_pos)).2
      simpa only [one_mul] using twentyOneFiftiethTailPolynomial_threshold_le he
    · rw [if_neg he]
      dsimp only [F]
      exact div_nonneg
        (twentyOneFiftiethTailPolynomial_nonneg (sq_nonneg _))
        twentyOneFiftiethTailPolynomial_threshold_pos.le
  have hprob := CertifiedJL.finitePMF_eventProbability_toReal_le_integral
    (rademacherPMF (Fin n)) event F hpoint
  have hE := twentyOneFiftiethTailPolynomial_expect_le_gaussian hn a ha
  have hintegral :
      (∫ bits, F bits ∂(rademacherPMF (Fin n)).toMeasure) =
        (𝔼 bits : Fin n → Bool,
          twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2)) /
            twentyOneFiftiethTailPolynomial A := by
    dsimp only [F]
    rw [integral_div, integral_rademacher_eq_expect]
  rw [hintegral] at hprob
  have hratio :
      (97154081 / 160000 : ℝ) /
          twentyOneFiftiethTailPolynomial (4691291049 / 800000000) < 57 / 1000 := by
    unfold twentyOneFiftiethTailPolynomial
    norm_num
  have hdiv := div_le_div_of_nonneg_right hE
    twentyOneFiftiethTailPolynomial_threshold_pos.le
  exact hprob.trans_lt (hdiv.trans_lt hratio)

theorem rademacherSum_normalized_twentyOneFiftieth_tail_toReal_lt_fintype
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (eventProbability (rademacherPMF ι)
      (fun bits => (4691291049 / 800000000 : ℝ) ≤
        (rademacherSum a bits) ^ 2)).toReal < 57 / 1000 := by
  classical
  let A : ℝ := 4691291049 / 800000000
  let event : (ι → Bool) → Prop := fun bits => A ≤ (rademacherSum a bits) ^ 2
  let F : (ι → Bool) → ℝ := fun bits =>
    twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2) / twentyOneFiftiethTailPolynomial A
  have hpoint (bits : ι → Bool) :
      (if event bits then (1 : ℝ) else 0) ≤ F bits := by
    by_cases he : event bits
    · rw [if_pos he]
      dsimp only [F]
      apply (le_div_iff₀ (by
        dsimp only [A]
        exact twentyOneFiftiethTailPolynomial_threshold_pos)).2
      simpa only [one_mul] using twentyOneFiftiethTailPolynomial_threshold_le he
    · rw [if_neg he]
      dsimp only [F]
      exact div_nonneg (twentyOneFiftiethTailPolynomial_nonneg (sq_nonneg _))
        twentyOneFiftiethTailPolynomial_threshold_pos.le
  have hprob := CertifiedJL.finitePMF_eventProbability_toReal_le_integral
    (rademacherPMF ι) event F hpoint
  have hE := twentyOneFiftiethTailPolynomial_expect_le_gaussian_fintype a ha
  have hintegral :
      (∫ bits, F bits ∂(rademacherPMF ι).toMeasure) =
        (𝔼 bits : ι → Bool,
          twentyOneFiftiethTailPolynomial ((rademacherSum a bits) ^ 2)) /
            twentyOneFiftiethTailPolynomial A := by
    dsimp only [F]
    rw [integral_div, integral_rademacher_eq_expect_fintype]
  rw [hintegral] at hprob
  have hratio :
      (97154081 / 160000 : ℝ) /
          twentyOneFiftiethTailPolynomial (4691291049 / 800000000) < 57 / 1000 := by
    unfold twentyOneFiftiethTailPolynomial
    norm_num
  have hdiv := div_le_div_of_nonneg_right hE
    twentyOneFiftiethTailPolynomial_threshold_pos.le
  exact hprob.trans_lt (hdiv.trans_lt hratio)

end CertifiedJL.SparseLInfLower21Over50
