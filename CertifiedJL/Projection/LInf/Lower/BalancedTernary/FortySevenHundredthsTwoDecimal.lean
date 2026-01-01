/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Spec
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap47Tail.Verified
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SingletonConditioning
import CertifiedJL.Model.Modular.CenteredGeometry
import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Probability.Product.RowTensorization
import CertifiedJL.Projection.Counterexamples.Shared.SparseThreeAtomCenteredArc
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwentyOneFiftiethTail
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwoDecimalMajorantAssembly
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwoDecimalTailBounds
import CertifiedJL.Statements.LInf.Lower

/-!
# Sharp two-decimal `47/100` sparse modular infinity lower tail
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL.TernaryLInfThresholdLower47Over100TwoDecimal

open Probability
open SparseLInfLowerTwoDecimal

def parametersAt (rows : ℕ) : LInfThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := rows
    coordinateCap :=
      { numerator := 47, denominator := 100, denominator_pos := by decide }
    modulusMargin := NonnegativeRatio.ofNat 2 }

def RowPass (q inputThreshold : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  10000 * (centeredMod q (∑ i, row i * w i)).natAbs ^ 2 ≤
    2209 * inputThreshold ^ 2

def Pass (q inputThreshold : ℕ) {m d : ℕ} (w : Fin d → ℤ)
    (J : Matrix (Fin m) (Fin d) ℤ) : Prop :=
  ∀ j, RowPass q inputThreshold w (J j)

def Small (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Prop :=
  10000 ^ 2 * sqNorm w < 4679 ^ 2 * q ^ 2

def Large (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Prop :=
  ∃ i, 47 * q < 100 * (w i).natAbs

def Diffuse (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Prop :=
  4679 ^ 2 * q ^ 2 ≤ 10000 ^ 2 * sqNorm w ∧
    ∀ i, 100 * (w i).natAbs ≤ 47 * q

def CentralRow (inputThreshold : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  10000 * (∑ i, row i * w i).natAbs ^ 2 ≤ 2209 * inputThreshold ^ 2

def WrapRow (q inputThreshold : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  100 * q ≤ 47 * inputThreshold + 100 * (∑ i, row i * w i).natAbs

def DiffuseArcRow (q : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  200 * (centeredMod q (∑ i, row i * w i)).natAbs ≤ 47 * q

theorem regime_trichotomy (q : ℕ) {d : ℕ} (w : Fin d → ℤ) :
    Small q w ∨ Large q w ∨ Diffuse q w := by
  by_cases hs : 10000 ^ 2 * sqNorm w < 4679 ^ 2 * q ^ 2
  · exact Or.inl hs
  · right
    by_cases hl : ∃ i, 47 * q < 100 * (w i).natAbs
    · exact Or.inl hl
    · exact Or.inr ⟨le_of_not_gt hs,
        fun i => le_of_not_gt (not_exists.mp hl i)⟩

theorem rowPass_implies_central_or_wrap
    {q d inputThreshold : ℕ} {w : Fin d → ℤ} (row : Fin d → ℤ)
    (hp : RowPass q inputThreshold w row) :
    CentralRow inputThreshold w row ∨ WrapRow q inputThreshold w row := by
  let z : ℤ := ∑ i, row i * w i
  by_cases hz : z = centeredMod q z
  · left
    unfold CentralRow RowPass at *
    change 10000 * z.natAbs ^ 2 ≤ 2209 * inputThreshold ^ 2
    change 10000 * (centeredMod q z).natAbs ^ 2 ≤
      2209 * inputThreshold ^ 2 at hp
    rwa [← hz] at hp
  · right
    have hgeometry := centeredMod_modulus_le_natAbs_add_of_ne hz
    have hr : 100 * (centeredMod q z).natAbs ≤ 47 * inputThreshold := by
      unfold RowPass at hp
      change 10000 * (centeredMod q z).natAbs ^ 2 ≤
        2209 * inputThreshold ^ 2 at hp
      nlinarith [sq_nonneg
        (100 * ((centeredMod q z).natAbs : ℤ) - 47 * (inputThreshold : ℤ))]
    unfold WrapRow
    change q ≤ z.natAbs + (centeredMod q z).natAbs at hgeometry
    change 100 * q ≤ 47 * inputThreshold + 100 * z.natAbs
    omega

theorem cap47TailPowerValue_eq (x : ℝ) :
    TrigonometricBernstein.rationalPowerValue
        TernaryLInfTwoDecimal.Cap47Tail.tailPower x =
      SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial x - 9460 := by
  rw [SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial_expanded]
  norm_num [TrigonometricBernstein.rationalPowerValue,
    TrigonometricBernstein.powerPolynomialQ,
    TernaryLInfTwoDecimal.Cap47Tail.tailPower, Finset.sum_range_succ]
  ring

theorem cap47TailPolynomial_ge {x : ℝ} (hx : (55589 / 10000 : ℝ) ≤ x) :
    (9460 : ℝ) ≤
      SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial x := by
  have hx' : ((((55589 / 10000 : ℚ)) : ℝ)) ≤ x := by
    norm_num at hx ⊢
    exact hx
  have h := TernaryLInfTwoDecimal.Cap47Tail.nonnegativeAbove hx'
  rw [cap47TailPowerValue_eq] at h
  linarith

theorem rademacherSum_normalized_tail_55589_over_10000_toReal_le_fintype
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (eventProbability (rademacherPMF ι)
      (fun bits => (55589 / 10000 : ℝ) ≤
        (rademacherSum a bits) ^ 2)).toReal ≤
          97154081 / 1513600000 := by
  classical
  let event : (ι → Bool) → Prop := fun bits =>
    (55589 / 10000 : ℝ) ≤ (rademacherSum a bits) ^ 2
  let F : (ι → Bool) → ℝ := fun bits =>
    SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial
      ((rademacherSum a bits) ^ 2) / 9460
  have hpoint (bits : ι → Bool) :
      (if event bits then (1 : ℝ) else 0) ≤ F bits := by
    by_cases he : event bits
    · rw [if_pos he]
      dsimp only [F]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 9460)).2
      simpa only [one_mul] using cap47TailPolynomial_ge he
    · rw [if_neg he]
      dsimp only [F]
      exact div_nonneg
        (SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial_nonneg
          (sq_nonneg _)) (by norm_num)
  have hprob := finitePMF_eventProbability_toReal_le_integral
    (rademacherPMF ι) event F hpoint
  have hE :=
    SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial_expect_le_gaussian_fintype
      a ha
  have hintegral :
      (∫ bits, F bits ∂(rademacherPMF ι).toMeasure) =
        (𝔼 bits : ι → Bool,
          SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial
            ((rademacherSum a bits) ^ 2)) / 9460 := by
    dsimp only [F]
    rw [integral_div, integral_rademacher_eq_expect_fintype]
  rw [hintegral] at hprob
  have hdiv := div_le_div_of_nonneg_right hE (by norm_num : (0 : ℝ) ≤ 9460)
  norm_num at hdiv ⊢
  exact hprob.trans hdiv

theorem central_row_probability_toReal_le {d inputThreshold : ℕ}
    (hcentral : TernaryLInfTwoDecimal.Cap47CentralCertificate)
    (w : Fin d → ℤ) (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) :
    (eventProbability (sparseRademacherRow d)
      (CentralRow inputThreshold w)).toReal ≤
        (TernaryLInfTwoDecimal.Cap47Central.expectationBound : ℝ) := by
  classical
  have hVpos : 0 < sqNorm w := (pow_pos hpositive 2).trans_le hnorm
  have hw : w ≠ 0 := (sqNorm_pos_iff w).1 hVpos
  apply central_event_probability_toReal_le w hw (CentralRow inputThreshold w)
    TernaryLInfTwoDecimal.Cap47Central.fourier
    hcentral.contractProof
  intro row
  by_cases hr : CentralRow inputThreshold w row
  · rw [if_pos hr]
    let v := integerEuclideanVector w
    have hv : v ≠ 0 := by
      intro hv0
      have hzero : sqNorm w = 0 := by
        have : ‖v‖ ^ 2 = 0 := by rw [hv0]; simp
        rw [norm_sq_integerEuclideanVector] at this
        exact_mod_cast this
      exact hw ((sqNorm_eq_zero_iff w).mp hzero)
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hnormSq : ‖v‖ ^ 2 = (sqNorm w : ℝ) := by
      simpa only [v] using norm_sq_integerEuclideanVector w
    have hbNorm : (inputThreshold : ℝ) ≤ ‖v‖ := by
      have hnormR : (inputThreshold : ℝ) ^ 2 ≤ (sqNorm w : ℝ) := by
        exact_mod_cast hnorm
      rw [← hnormSq] at hnormR
      nlinarith [norm_nonneg v]
    have hrR : (100 : ℝ) * |((∑ i, row i * w i : ℤ) : ℝ)| ≤
        47 * inputThreshold := by
      unfold CentralRow at hr
      have hcast : (10000 : ℝ) * |((∑ i, row i * w i : ℤ) : ℝ)| ^ 2 ≤
          2209 * (inputThreshold : ℝ) ^ 2 := by
        have hcastNat :
            ((10000 * (∑ i, row i * w i).natAbs ^ 2 : ℕ) : ℝ) ≤
              ((2209 * inputThreshold ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast hr
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
          Nat.cast_natAbs, Int.cast_abs] using hcastNat
      nlinarith [abs_nonneg ((∑ i, row i * w i : ℤ) : ℝ)]
    have hphase : |centralPhase w row| ≤
        (111 / 100 : ℝ) * (47 / 100 : ℝ) * Real.sqrt 2 := by
      simp only [centralPhase]
      rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
        abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_pos hn,
        euclideanRowDot_integerEuclideanVector]
      apply (div_le_iff₀ hn).2
      nlinarith [Real.sqrt_nonneg 2]
    have hcapPi : ((111 / 100 : ℝ) * (47 / 100 : ℝ) * Real.sqrt 2) ≤
        Real.pi := by
      have hsqrt : Real.sqrt 2 < 3 / 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_nonneg 2]
      nlinarith [Real.pi_gt_three]
    have hcosMono : Real.cos
        ((111 / 100 : ℝ) * (47 / 100 : ℝ) * Real.sqrt 2) ≤
          Real.cos (centralPhase w row) := by
      calc
        _ ≤ Real.cos |centralPhase w row| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hcapPi hphase
        _ = _ := Real.cos_abs _
    apply hcentral.cosineDominatesOne
    have hc := cos_central47_lower
    norm_num at hc ⊢
    rw [show (111 / 100 : ℝ) * (47 / 100 : ℝ) = 5217 / 10000 by norm_num]
      at hcosMono
    exact hc.le.trans hcosMono
  · rw [if_neg hr]
    exact hcentral.cosineNonnegative _

theorem diffuseArc_row_probability_toReal_lt {q d : ℕ}
    (hdiffuse : TernaryLInfTwoDecimal.Cap47DiffuseCertificate)
    (w : Fin d → ℤ) (hqpos : 0 < q) (hd : Diffuse q w) :
    (eventProbability (sparseRademacherRow d) (DiffuseArcRow q w)).toReal <
      37831 / 50000 := by
  classical
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hpoint (row : Fin d → ℤ) :
      (if DiffuseArcRow q w row then (1 : ℝ) else 0) ≤
        TrigonometricBernstein.rationalCosineValue
          TernaryLInfTwoDecimal.Cap47Diffuse.fourier
          (diffusePhase (q := q) w row) := by
    by_cases hp : DiffuseArcRow q w row
    · rw [if_pos hp]
      let z : ℤ := ∑ i, row i * w i
      let r : ℤ := centeredMod q z
      have hr : (200 : ℝ) * |(r : ℝ)| ≤ 47 * q := by
        have hc : 200 * r.natAbs ≤ 47 * q := hp
        have hc' : ((200 * r.natAbs : ℕ) : ℝ) ≤ ((47 * q : ℕ) : ℝ) := by
          exact_mod_cast hc
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_natAbs,
          Int.cast_abs] using hc'
      have habs : |(2 * Real.pi / (q : ℝ)) * (r : ℝ)| ≤
          47 * Real.pi / 100 := by
        rw [abs_mul, abs_div,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), abs_of_pos hqr]
        have hratio : |(r : ℝ)| / (q : ℝ) ≤ 47 / 200 := by
          apply (div_le_iff₀ hqr).2
          nlinarith [hr]
        calc
          2 * Real.pi / (q : ℝ) * |(r : ℝ)| =
              (2 * Real.pi) * (|(r : ℝ)| / (q : ℝ)) := by ring
          _ ≤ (2 * Real.pi) * (47 / 200) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = 47 * Real.pi / 100 := by ring
      have hcosPhase : Real.cos (diffusePhase (q := q) w row) =
          Real.cos ((2 * Real.pi / (q : ℝ)) * (r : ℝ)) := by
        simp only [diffusePhase]
        rw [euclideanRowDot_integerEuclideanVector]
        exact cosine_twoPiOverModulus_centeredMod (Nat.ne_of_gt hqpos) z
      have hcapPi : (47 * Real.pi / 100 : ℝ) ≤ Real.pi := by
        nlinarith [Real.pi_pos]
      have hcosMono : Real.cos (47 * Real.pi / 100) ≤
          Real.cos ((2 * Real.pi / (q : ℝ)) * (r : ℝ)) := by
        calc
          _ ≤ Real.cos |(2 * Real.pi / (q : ℝ)) * (r : ℝ)| :=
            Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hcapPi habs
          _ = _ := Real.cos_abs _
      apply hdiffuse.cosineDominatesOne
      rw [hcosPhase]
      have hc := cos_diffuse47_lower
      norm_num at hc ⊢
      rw [show 47 * Real.pi / 100 = Real.pi * (47 / 100 : ℝ) by ring]
        at hcosMono
      exact hc.le.trans hcosMono
    · rw [if_neg hp]
      exact hdiffuse.cosineNonnegative _
  let p : PMF (SparseRowSeed d) := PMF.uniformOfFintype (SparseRowSeed d)
  have hmomentOne :
      (∫ seed, Real.cos ((1 : ℝ) *
        diffusePhase (q := q) w (sparseRow seed)) ∂p.toMeasure) ≤
          (TernaryLInfTwoDecimal.Cap47Diffuse.diffuseMomentBound : ℝ) := by
    have hmoment := sparseRowSeed_integer_cosineMoment_eq_product w
      (2 * Real.pi / (q : ℝ))
    rw [show (∫ seed, Real.cos ((1 : ℝ) *
        diffusePhase (q := q) w (sparseRow seed)) ∂p.toMeasure) =
      ∏ i, Real.cos (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 by
        convert hmoment using 1
        · congr 1
          funext seed
          congr 1
          simp only [diffusePhase]
          ring
        · apply Finset.prod_congr rfl
          intro i _
          congr 2
          ring]
    have hfactor (i : Fin d) :
        Real.cos (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 ≤
          Real.exp (-((Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2)) := by
      apply cos_sq_le_exp_neg_sq
      have hi : (100 : ℝ) * |(w i : ℝ)| ≤ 47 * q := by
        rw [show |(w i : ℝ)| = (((w i).natAbs : ℕ) : ℝ) by simp]
        exact_mod_cast hd.2 i
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hqr]
      have hpi : 47 * Real.pi / 100 < Real.pi / 2 := by
        nlinarith [Real.pi_pos]
      apply lt_of_le_of_lt _ hpi
      apply (div_le_iff₀ hqr).2
      nlinarith [Real.pi_pos]
    have hproduct :
        (∏ i, Real.cos (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2) ≤
          ∏ i, Real.exp (-((Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2)) := by
      exact Finset.prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => hfactor i)
    have hsum : Real.pi ^ 2 * (4679 / 10000 : ℝ) ^ 2 ≤
        ∑ i, (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 := by
      have hdR : (4679 : ℝ) ^ 2 * q ^ 2 ≤
          (10000 : ℝ) ^ 2 * (sqNorm w : ℝ) := by exact_mod_cast hd.1
      have hq2 : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hqr
      rw [show (∑ i, (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2) =
          Real.pi ^ 2 / (q : ℝ) ^ 2 * (sqNorm w : ℝ) by
        simp_rw [div_pow, mul_pow]
        rw [← Finset.sum_div, ← Finset.mul_sum, ← realCast_sqNorm]
        ring]
      rw [show Real.pi ^ 2 / (q : ℝ) ^ 2 * (sqNorm w : ℝ) =
        (Real.pi ^ 2 * (sqNorm w : ℝ)) / (q : ℝ) ^ 2 by ring]
      apply (le_div_iff₀ hq2).2
      nlinarith [sq_nonneg Real.pi]
    have hstrict : (∏ i, Real.cos
        (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2) < 2881 / 25000 := calc
      _ ≤ ∏ i, Real.exp (-((Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2)) := hproduct
      _ = Real.exp (-∑ i,
          (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_neg_distrib]
      _ ≤ Real.exp (-(Real.pi ^ 2 * (4679 / 10000 : ℝ) ^ 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ < 2881 / 25000 := exp_neg_diffuse47_lt
    norm_num [TernaryLInfTwoDecimal.Cap47Diffuse.diffuseMomentBound]
      at hstrict ⊢
    exact hstrict.le
  have hbound := diffuse_event_probability_toReal_le w (DiffuseArcRow q w)
    TernaryLInfTwoDecimal.Cap47Diffuse.fourier
    hdiffuse.contractProof hpoint hmomentOne
  exact hbound.trans_lt (by
    norm_num [TernaryLInfTwoDecimal.Cap47Diffuse.expectationBound])

theorem wrap_implies_tail_55589_over_10000_lt
    {q d inputThreshold : ℕ} {w : Fin d → ℤ}
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) (hs : Small q w)
    {row : Fin d → ℤ} (hr : WrapRow q inputThreshold w row) :
    (55589 / 10000 : ℝ) <
      (Real.sqrt 2 * euclideanRowDot row (integerEuclideanVector w) /
        ‖integerEuclideanVector w‖) ^ 2 := by
  let v := integerEuclideanVector w
  have hVpos : 0 < sqNorm w := (pow_pos hpositive 2).trans_le hnorm
  have hw : w ≠ 0 := (sqNorm_pos_iff w).1 hVpos
  have hv : v ≠ 0 := by
    intro hv0
    have hzero : sqNorm w = 0 := by
      have : ‖v‖ ^ 2 = 0 := by rw [hv0]; simp
      rw [norm_sq_integerEuclideanVector] at this
      exact_mod_cast this
    exact hw ((sqNorm_eq_zero_iff w).mp hzero)
  have hnpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnormSq : ‖v‖ ^ 2 = (sqNorm w : ℝ) := by
    simpa only [v] using norm_sq_integerEuclideanVector w
  have hbNorm : (inputThreshold : ℝ) ≤ ‖v‖ := by
    have hnormR : (inputThreshold : ℝ) ^ 2 ≤ (sqNorm w : ℝ) := by
      exact_mod_cast hnorm
    rw [← hnormSq] at hnormR
    nlinarith [norm_nonneg v]
  have hsR : (10000 : ℝ) ^ 2 * (sqNorm w : ℝ) <
      (4679 : ℝ) ^ 2 * q ^ 2 := by
    exact_mod_cast hs
  have hqNorm : (10000 : ℝ) * ‖v‖ < 4679 * q := by
    rw [← hnormSq] at hsR
    nlinarith [norm_nonneg v]
  have hrR : (100 : ℝ) * q ≤ 47 * inputThreshold +
      100 * |((∑ i, row i * w i : ℤ) : ℝ)| := by
    unfold WrapRow at hr
    have hcast : ((100 * q : ℕ) : ℝ) ≤
        ((47 * inputThreshold + 100 * (∑ i, row i * w i).natAbs : ℕ) : ℝ) := by
      exact_mod_cast hr
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_natAbs, Int.cast_abs] using hcast
  have hratio : (780087 : ℝ) * ‖v‖ <
      467900 * |((∑ i, row i * w i : ℤ) : ℝ)| := by
    nlinarith
  let Y : ℝ := Real.sqrt 2 * euclideanRowDot row v / ‖v‖
  have hY : (780087 * Real.sqrt 2 / 467900 : ℝ) < |Y| := by
    dsimp [Y]
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2),
      abs_of_pos hnpos, euclideanRowDot_integerEuclideanVector]
    apply (lt_div_iff₀ hnpos).2
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hconstant : (780087 * Real.sqrt 2 / 467900 : ℝ) ^ 2 =
      608535727569 / 109465205000 := by
    rw [div_pow, mul_pow, hsqrt]
    norm_num
  have hsq : (780087 * Real.sqrt 2 / 467900 : ℝ) ^ 2 < |Y| ^ 2 :=
    pow_lt_pow_left₀ hY (by positivity) (by norm_num)
  rw [hconstant, sq_abs] at hsq
  change (55589 / 10000 : ℝ) <
    (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2
  exact lt_trans
    (by norm_num : (55589 / 10000 : ℝ) < 608535727569 / 109465205000) hsq

theorem wrap_row_probability_toReal_le
    {q d inputThreshold : ℕ} (w : Fin d → ℤ)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) (hs : Small q w) :
    (eventProbability (sparseRademacherRow d)
      (WrapRow q inputThreshold w)).toReal ≤
        97154081 / 1513600000 := by
  let v := integerEuclideanVector w
  have hVpos : 0 < sqNorm w := (pow_pos hpositive 2).trans_le hnorm
  have hw : w ≠ 0 := (sqNorm_pos_iff w).1 hVpos
  have hv : v ≠ 0 := by
    intro hv0
    have hzero : sqNorm w = 0 := by
      have : ‖v‖ ^ 2 = 0 := by rw [hv0]; simp
      rw [norm_sq_integerEuclideanVector] at this
      exact_mod_cast this
    exact hw ((sqNorm_eq_zero_iff w).mp hzero)
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact hw (Subsingleton.elim _ _)
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdpos
  have hmono : eventProbability (sparseRademacherRow d)
      (WrapRow q inputThreshold w) ≤
      eventProbability (sparseRademacherRow d)
        (fun row => (55589 / 10000 : ℝ) ≤
          (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2) :=
    eventProbability_mono (sparseRademacherRow d)
      (fun row (hr : WrapRow q inputThreshold w row) =>
        (wrap_implies_tail_55589_over_10000_lt hpositive hnorm hs hr).le)
  have heq : eventProbability (sparseRademacherRow d)
        (fun row => (55589 / 10000 : ℝ) ≤
          (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2) =
      eventProbability (rademacherPMF (Fin d × Fin 2))
        (fun bits => (55589 / 10000 : ℝ) ≤
          (rademacherSum (normalizedDuplicatedCoefficient v) bits) ^ 2) := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    calc
      eventProbability ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRow)
          (fun row => (55589 / 10000 : ℝ) ≤
            (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2) =
        eventProbability
          ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRowSeedSigns)
          (fun bits => (55589 / 10000 : ℝ) ≤
            (rademacherSum (normalizedDuplicatedCoefficient v) bits) ^ 2) := by
          apply eventProbability_map_congr
          intro seed
          rw [rademacherSum_normalizedDuplicatedCoefficient seed v hv]
      _ = _ := by
        rw [map_uniformSparseSeed_signs]
        unfold rademacherPMF
        rw [uniformPiPMF_eq_uniformOfFintype]
  have htail :=
    rademacherSum_normalized_tail_55589_over_10000_toReal_le_fintype
      (normalizedDuplicatedCoefficient v)
      (sum_sq_normalizedDuplicatedCoefficient v hv)
  have hre := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmono
  change (eventProbability (sparseRademacherRow d)
      (WrapRow q inputThreshold w)).toReal ≤
    (eventProbability (sparseRademacherRow d)
      (fun row => (55589 / 10000 : ℝ) ≤
        (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2)).toReal at hre
  rw [heq] at hre
  exact hre.trans htail

theorem small_row_probability_toReal_lt
    {q d inputThreshold : ℕ} (w : Fin d → ℤ)
    (hcentral : TernaryLInfTwoDecimal.Cap47CentralCertificate)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) (hs : Small q w) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal < 37831 / 50000 := by
  have hi : eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w) ≤
      eventProbability (sparseRademacherRow d)
        (fun row => CentralRow inputThreshold w row ∨
          WrapRow q inputThreshold w row) :=
    eventProbability_mono (sparseRademacherRow d)
      (fun row hp => rowPass_implies_central_or_wrap row hp)
  have hu := eventProbability_or_toReal_le (sparseRademacherRow d)
    (CentralRow inputThreshold w) (WrapRow q inputThreshold w)
  have hc := central_row_probability_toReal_le hcentral w hpositive hnorm
  have ht := wrap_row_probability_toReal_le w hpositive hnorm hs
  calc
    (eventProbability (sparseRademacherRow d)
        (RowPass q inputThreshold w)).toReal ≤
      (eventProbability (sparseRademacherRow d)
        (fun row => CentralRow inputThreshold w row ∨
          WrapRow q inputThreshold w row)).toReal :=
        ENNReal.toReal_mono (PMF.apply_ne_top _ _) hi
    _ ≤ (eventProbability (sparseRademacherRow d)
          (CentralRow inputThreshold w)).toReal +
        (eventProbability (sparseRademacherRow d)
          (WrapRow q inputThreshold w)).toReal := hu
    _ ≤ (TernaryLInfTwoDecimal.Cap47Central.expectationBound : ℝ) +
        97154081 / 1513600000 := add_le_add hc ht
    _ < 37831 / 50000 := by
      norm_num [TernaryLInfTwoDecimal.Cap47Central.expectationBound]

theorem diffuse_row_probability_toReal_lt
    {q d inputThreshold : ℕ} (w : Fin d → ℤ) (hqpos : 0 < q)
    (hdiffuse : TernaryLInfTwoDecimal.Cap47DiffuseCertificate)
    (hmargin : 2 * inputThreshold ≤ q) (hd : Diffuse q w) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal < 37831 / 50000 := by
  have hmono : eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w) ≤
      eventProbability (sparseRademacherRow d) (DiffuseArcRow q w) := by
    apply eventProbability_mono
    intro row hp
    unfold RowPass at hp
    unfold DiffuseArcRow
    nlinarith [sq_nonneg
      (100 * ((centeredMod q (∑ i, row i * w i)).natAbs : ℤ) -
        47 * (inputThreshold : ℤ))]
  exact (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmono).trans_lt
    (diffuseArc_row_probability_toReal_lt hdiffuse w hqpos hd)

theorem coordinate_half_modulus_of_centeredInput
    {q d : ℕ} {w : Fin d → ℤ} (hcentered : CenteredInput q w)
    (i : Fin d) : 2 * (w i).natAbs ≤ q := by
  have hi := hcentered i
  simp only [centeredInterval, Set.mem_Icc] at hi
  have habs : |w i| ≤ ((q / 2 : ℕ) : ℤ) := (abs_le).2 hi
  have hnat : (w i).natAbs ≤ q / 2 := by
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  calc
    2 * (w i).natAbs ≤ 2 * (q / 2) := Nat.mul_le_mul_left 2 hnat
    _ ≤ q := Nat.mul_div_le q 2

theorem large_row_probability_toReal_le_half
    {q d inputThreshold : ℕ} (w : Fin d → ℤ)
    (hcentered : CenteredInput q w) (hmargin : 2 * inputThreshold ≤ q)
    (hl : Large q w) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal ≤ 1 / 2 := by
  obtain ⟨i, hi⟩ := hl
  apply sparseRademacherRow_eventProbability_toReal_le_of_complFirst
    (singletonCoordinateMask i) (RowPass q inputThreshold w) (1 / 2 : ℝ)
  intro other
  let shift := sparseRowSeedComplDot (singletonCoordinateMask i) other w
  have hevent :
      eventProbability
        ((PMF.uniformOfFintype
          (SparseRowSeedPart (singletonCoordinateMask i))).map
          (fun selected => sparseRow
            (joinSparseRowSeed (singletonCoordinateMask i) selected other)))
        (RowPass q inputThreshold w) =
      eventProbability
        ((PMF.uniformOfFintype
          (SparseRowSeedPart (singletonCoordinateMask i))).map
          (sparseRowSingletonSeedEquiv i))
        (fun bits => 10000 *
          (centeredMod q (shift + sparseBit bits * w i)).natAbs ^ 2 ≤
            2209 * inputThreshold ^ 2) := by
    apply eventProbability_map_congr
    intro selected
    unfold RowPass
    rw [sparseRow_join_singleton_dot]
  rw [hevent, map_uniformSparseRowSingletonSeed]
  have hpull :
      eventProbability (PMF.uniformOfFintype (Bool × Bool))
          (fun bits => 10000 *
            (centeredMod q (shift + sparseBit bits * w i)).natAbs ^ 2 ≤
              2209 * inputThreshold ^ 2) =
        eventProbability sparseEntryPMF
          (fun x => 10000 *
            (centeredMod q (shift + x * w i)).natAbs ^ 2 ≤
              2209 * inputThreshold ^ 2) := by
    unfold sparseEntryPMF eventProbability
    rw [PMF.map_comp]
    rfl
  rw [hpull]
  have hmono : eventProbability sparseEntryPMF
      (fun x => 10000 *
        (centeredMod q (shift + x * w i)).natAbs ^ 2 ≤
          2209 * inputThreshold ^ 2) ≤
      eventProbability sparseEntryPMF
        (fun x => ScaledCenteredArcPass q 100 (47 * inputThreshold)
          (shift + x * w i)) := by
    apply eventProbability_mono
    intro x hx
    unfold ScaledCenteredArcPass
    nlinarith [sq_nonneg
      (100 * ((centeredMod q (shift + x * w i)).natAbs : ℤ) -
        47 * (inputThreshold : ℤ))]
  apply (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmono).trans
  apply sparseEntry_scaledCenteredArcPass_toReal_le_half_of_centered
    (q := q) (scale := 100) (radius := 47 * inputThreshold) shift (w i)
    (coordinate_half_modulus_of_centeredInput hcentered i)
  omega

theorem row_probability_toReal_lt
    {q d inputThreshold : ℕ} (w : Fin d → ℤ)
    (hcentral : TernaryLInfTwoDecimal.Cap47CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap47DiffuseCertificate)
    (hpositive : 0 < inputThreshold) (hcentered : CenteredInput q w)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hmargin : 2 * inputThreshold ≤ q) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal < 37831 / 50000 := by
  have hqpos : 0 < q := by omega
  rcases regime_trichotomy q w with hs | hl | hd
  · exact small_row_probability_toReal_lt w hcentral hpositive hnorm hs
  · exact (large_row_probability_toReal_le_half w hcentered hmargin hl).trans_lt
      (by norm_num)
  · exact diffuse_row_probability_toReal_lt w hqpos hdiffuse hmargin hd

theorem rows_probability_lt_of_pow_bound
    {rows q d inputThreshold : ℕ} {budget : ENNReal}
    (w : Fin d → ℤ) (hpositive : 0 < inputThreshold)
    (hcentral : TernaryLInfTwoDecimal.Cap47CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap47DiffuseCertificate)
    (hcentered : CenteredInput q w)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hmargin : 2 * inputThreshold ≤ q)
    (hpow : ((37831 : ENNReal) / 50000) ^ rows < budget) :
    eventProbability (sparseRademacherMatrix rows d)
      (Pass q inputThreshold w) < budget := by
  change eventProbability (sparseRademacherMatrix rows d)
    (fun J => ∀ j, RowPass q inputThreshold w (J j)) < budget
  apply (sparseRademacherMatrix_eventProbability_allRows_le_pow
    rows d (RowPass q inputThreshold w) ((37831 : ENNReal) / 50000) ?_).trans_lt
    hpow
  apply finitePMF_eventProbability_le_of_toReal_le
    (sparseRademacherRow d) (RowPass q inputThreshold w) (by finiteness)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using
    (row_probability_toReal_lt w hcentral hdiffuse hpositive hcentered
      hnorm hmargin).le

set_option maxRecDepth 100000

set_option exponentiation.threshold 2048 in
theorem rowBound_pow_rows512_bits206 :
    ((37831 : ENNReal) / 50000) ^ 512 < failureTarget 206 := by
  rw [← ENNReal.toReal_lt_toReal (by finiteness)
    (by unfold failureTarget; finiteness)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    failureTarget, ENNReal.toReal_inv]
  norm_num [zpow_neg]

theorem ternaryLInfThresholdLower47Over100_of_pow_bound
    (rows bits : ℕ)
    (hcentral : TernaryLInfTwoDecimal.Cap47CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap47DiffuseCertificate)
    (hpow : ((37831 : ENNReal) / 50000) ^ rows < failureTarget bits) :
    LInfThresholdLowerTailAt (parametersAt rows) (failureTarget bits) := by
  intro q d w inputThreshold _hq hcentered hpositive hnorm hmodulus
  have hnorm' : inputThreshold ^ 2 ≤ sqNorm w := by
    simpa [InputThresholdAtMostNorm] using hnorm
  have hmargin : 2 * inputThreshold ≤ q := by
    simpa [parametersAt, InputThresholdWithinModulus,
      NonnegativeRatio.ofNat] using hmodulus
  simp only [parametersAt, ProjectionDistribution.matrixPMF_balancedTernary]
  rw [eventProbability_congr (sparseRademacherMatrix rows d)
    (event' := Pass q inputThreshold w) (by
      intro J
      simp [LInfThresholdSmallProjection, Pass, RowPass, rowDot])]
  exact rows_probability_lt_of_pow_bound w hpositive hcentral hdiffuse
    hcentered hnorm' hmargin hpow

theorem ternaryLInfThresholdLower47Over100_rows512_bits206_of_certificates
    (hcentral : TernaryLInfTwoDecimal.Cap47CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap47DiffuseCertificate) :
    LInfThresholdLowerTailAt (parametersAt 512) (failureTarget 206) :=
  ternaryLInfThresholdLower47Over100_of_pow_bound 512 206 hcentral hdiffuse
    rowBound_pow_rows512_bits206

set_option maxRecDepth 1000

end CertifiedJL.TernaryLInfThresholdLower47Over100TwoDecimal
