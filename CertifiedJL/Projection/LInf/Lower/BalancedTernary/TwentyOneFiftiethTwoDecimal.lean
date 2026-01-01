/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Spec
import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Replay.Cap42Tail.Verified
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.CosineMoments
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SingletonConditioning
import CertifiedJL.Model.Modular.CenteredGeometry
import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Probability.Finite.IidQuadratic
import CertifiedJL.Probability.Finite.PMF
import CertifiedJL.Analysis.Fourier.NormalizedCosineProduct
import CertifiedJL.Probability.Product.RowTensorization
import CertifiedJL.Projection.Counterexamples.Shared.SparseThreeAtomCenteredArc
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwoDecimalAnalytic
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwentyOneFiftiethTail
import CertifiedJL.Statements.LInf.Lower
import CertifiedJL.Statements.Shared.Input

/-!
# Sharp two-decimal `21/50` sparse modular infinity lower tail

This is the proof-specific layer for the new `13939/20000` one-row target.
Unlike the legacy theorem, the small/diffuse split is made directly for the
public-threshold statement, so the wrap threshold retains all available
slack.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal

open Probability
open SparseLInfLowerTwoDecimal

def parametersAt (rows : ℕ) : LInfThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := rows
    coordinateCap :=
      { numerator := 21, denominator := 50, denominator_pos := by decide }
    modulusMargin := NonnegativeRatio.ofNat 2 }

def RowPass (q inputThreshold : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  2500 * (centeredMod q (∑ i, row i * w i)).natAbs ^ 2 ≤
    441 * inputThreshold ^ 2

def Pass (q inputThreshold : ℕ) {m d : ℕ} (w : Fin d → ℤ)
    (J : Matrix (Fin m) (Fin d) ℤ) : Prop :=
  ∀ j, RowPass q inputThreshold w (J j)

def Small (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Prop :=
  2000 ^ 2 * sqNorm w < 929 ^ 2 * q ^ 2

def Large (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Prop :=
  ∃ i, 21 * q < 50 * (w i).natAbs

def Diffuse (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Prop :=
  929 ^ 2 * q ^ 2 ≤ 2000 ^ 2 * sqNorm w ∧
    ∀ i, 50 * (w i).natAbs ≤ 21 * q

def DiffuseArcRow (q : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  100 * (centeredMod q (∑ i, row i * w i)).natAbs ≤ 21 * q

theorem regime_trichotomy (q : ℕ) {d : ℕ} (w : Fin d → ℤ) :
    Small q w ∨ Large q w ∨ Diffuse q w := by
  by_cases hs : 2000 ^ 2 * sqNorm w < 929 ^ 2 * q ^ 2
  · exact Or.inl hs
  · right
    by_cases hl : ∃ i, 21 * q < 50 * (w i).natAbs
    · exact Or.inl hl
    · exact Or.inr ⟨le_of_not_gt hs,
        fun i => le_of_not_gt (not_exists.mp hl i)⟩

def CentralRow (inputThreshold : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  2500 * (∑ i, row i * w i).natAbs ^ 2 ≤ 441 * inputThreshold ^ 2

/-- Keeping the public threshold in this event, instead of replacing it by
`q/2`, is what yields the sharp wrap threshold `2(1/s-c)^2`. -/
def WrapRow (q inputThreshold : ℕ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : Prop :=
  50 * q ≤ 21 * inputThreshold + 50 * (∑ i, row i * w i).natAbs

theorem rowPass_implies_central_or_wrap
    {q d inputThreshold : ℕ} {w : Fin d → ℤ} (row : Fin d → ℤ)
    (hp : RowPass q inputThreshold w row) :
    CentralRow inputThreshold w row ∨ WrapRow q inputThreshold w row := by
  let z : ℤ := ∑ i, row i * w i
  by_cases hz : z = centeredMod q z
  · left
    unfold CentralRow RowPass at *
    change 2500 * z.natAbs ^ 2 ≤ 441 * inputThreshold ^ 2
    change 2500 * (centeredMod q z).natAbs ^ 2 ≤
      441 * inputThreshold ^ 2 at hp
    rwa [← hz] at hp
  · right
    have hgeometry := centeredMod_modulus_le_natAbs_add_of_ne hz
    have hr : 50 * (centeredMod q z).natAbs ≤ 21 * inputThreshold := by
      unfold RowPass at hp
      change 2500 * (centeredMod q z).natAbs ^ 2 ≤
        441 * inputThreshold ^ 2 at hp
      nlinarith [sq_nonneg
        (50 * ((centeredMod q z).natAbs : ℤ) - 21 * (inputThreshold : ℤ))]
    unfold WrapRow
    change q ≤ z.natAbs + (centeredMod q z).natAbs at hgeometry
    change 50 * q ≤ 21 * inputThreshold + 50 * z.natAbs
    omega

theorem cap42TailPowerValue_eq (x : ℝ) :
    TrigonometricBernstein.rationalPowerValue
        TernaryLInfTwoDecimal.Cap42Tail.tailPower x =
      SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial x - 11180 := by
  rw [SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial_expanded]
  norm_num [TrigonometricBernstein.rationalPowerValue,
    TrigonometricBernstein.powerPolynomialQ,
    TernaryLInfTwoDecimal.Cap42Tail.tailPower, Finset.sum_range_succ]
  ring

theorem cap42TailPolynomial_ge {x : ℝ} (hx : 6 ≤ x) :
    (11180 : ℝ) ≤
      SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial x := by
  have h := TernaryLInfTwoDecimal.Cap42Tail.nonnegativeAbove hx
  rw [cap42TailPowerValue_eq] at h
  linarith

/-- Degree-ten Markov bound at the rounded threshold `Y² ≥ 6`. -/
theorem rademacherSum_normalized_tail_six_toReal_le_fintype
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (eventProbability (rademacherPMF ι)
      (fun bits => (6 : ℝ) ≤ (rademacherSum a bits) ^ 2)).toReal ≤
        97154081 / 1788800000 := by
  classical
  let event : (ι → Bool) → Prop := fun bits =>
    (6 : ℝ) ≤ (rademacherSum a bits) ^ 2
  let F : (ι → Bool) → ℝ := fun bits =>
    SparseLInfLower21Over50.twentyOneFiftiethTailPolynomial
      ((rademacherSum a bits) ^ 2) / 11180
  have hpoint (bits : ι → Bool) :
      (if event bits then (1 : ℝ) else 0) ≤ F bits := by
    by_cases he : event bits
    · rw [if_pos he]
      dsimp only [F]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 11180)).2
      simpa only [one_mul] using cap42TailPolynomial_ge he
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
            ((rademacherSum a bits) ^ 2)) / 11180 := by
    dsimp only [F]
    rw [integral_div,
      SparseLInfLower21Over50.integral_rademacher_eq_expect_fintype]
  rw [hintegral] at hprob
  have hdiv := div_le_div_of_nonneg_right hE (by norm_num : (0 : ℝ) ≤ 11180)
  norm_num at hdiv ⊢
  exact hprob.trans hdiv

/-- The generated degree-73 central majorant bounds the unwrapped public
threshold event. -/
theorem central_row_probability_toReal_le {d inputThreshold : ℕ}
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (w : Fin d → ℤ) (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) :
    (eventProbability (sparseRademacherRow d)
      (CentralRow inputThreshold w)).toReal ≤
        (TernaryLInfTwoDecimal.Cap42Central.expectationBound : ℝ) := by
  classical
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
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let p : PMF (SparseRowSeed d) := PMF.uniformOfFintype (SparseRowSeed d)
  let phase : SparseRowSeed d → ℝ := fun seed =>
    (111 / 100 : ℝ) * Real.sqrt 2 *
      euclideanRowDot (sparseRow seed) v / ‖v‖
  let event : SparseRowSeed d → Prop :=
    fun seed => CentralRow inputThreshold w (sparseRow seed)
  have heventPhase (seed : SparseRowSeed d) (hr : event seed) :
      |phase seed| ≤ (111 / 100 : ℝ) * (21 / 50 : ℝ) * Real.sqrt 2 := by
    have hnormSqV : ‖v‖ ^ 2 = (sqNorm w : ℝ) := by
      simpa only [v] using norm_sq_integerEuclideanVector w
    have hthresholdNorm : (inputThreshold : ℝ) ≤ ‖v‖ := by
      have hnormR : (inputThreshold : ℝ) ^ 2 ≤ (sqNorm w : ℝ) := by
        exact_mod_cast hnorm
      rw [← hnormSqV] at hnormR
      nlinarith [norm_nonneg v]
    have hrCast : (50 : ℝ) *
        |((∑ i, sparseRow seed i * w i : ℤ) : ℝ)| ≤
          21 * inputThreshold := by
      unfold event CentralRow at hr
      have hcast : (2500 : ℝ) *
          |((∑ i, sparseRow seed i * w i : ℤ) : ℝ)| ^ 2 ≤
            441 * (inputThreshold : ℝ) ^ 2 := by
        have hcastNat :
            ((2500 * (∑ i, sparseRow seed i * w i).natAbs ^ 2 : ℕ) : ℝ) ≤
              ((441 * inputThreshold ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast hr
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
          Nat.cast_natAbs, Int.cast_abs] using hcastNat
      nlinarith [abs_nonneg ((∑ i, sparseRow seed i * w i : ℤ) : ℝ)]
    dsimp [phase]
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
      abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_pos hn,
      euclideanRowDot_integerEuclideanVector]
    apply (div_le_iff₀ hn).2
    nlinarith [Real.sqrt_nonneg 2]
  have hpoint (seed : SparseRowSeed d) :
      (if event seed then (1 : ℝ) else 0) ≤
        TrigonometricBernstein.rationalCosineValue
          TernaryLInfTwoDecimal.Cap42Central.fourier (phase seed) := by
    by_cases hr : event seed
    · rw [if_pos hr]
      have hphase := heventPhase seed hr
      have hcapPi : ((111 / 100 : ℝ) * (21 / 50 : ℝ) * Real.sqrt 2) ≤
          Real.pi := by
        have hsqrt : Real.sqrt 2 < 3 / 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
            Real.sqrt_nonneg 2]
        nlinarith [Real.pi_gt_three]
      have hcosMono :
          Real.cos ((111 / 100 : ℝ) * (21 / 50 : ℝ) * Real.sqrt 2) ≤
            Real.cos (phase seed) := by
        calc
          _ ≤ Real.cos |phase seed| :=
            Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hcapPi hphase
          _ = _ := Real.cos_abs _
      apply hcentral.cosineDominatesOne
      have hc := cos_central42_lower
      norm_num at hc ⊢
      rw [show (111 / 100 : ℝ) * (21 / 50 : ℝ) = 2331 / 5000 by norm_num]
        at hcosMono
      exact hc.le.trans hcosMono
    · rw [if_neg hr]
      exact hcentral.cosineNonnegative _
  have hprobSeed := finitePMF_eventProbability_toReal_le_integral p event
    (fun seed => TrigonometricBernstein.rationalCosineValue
      TernaryLInfTwoDecimal.Cap42Central.fourier (phase seed)) hpoint
  have heventMap :
      eventProbability (sparseRademacherRow d) (CentralRow inputThreshold w) =
        eventProbability p event := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    unfold eventProbability
    rw [PMF.map_comp]
    rfl
  have hmoment (j : ℕ) :
      ∫ seed, Real.cos ((j : ℝ) * phase seed) ∂p.toMeasure =
        ∏ i, Real.cos
          ((j : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
            (w i : ℝ) / ‖v‖) ^ 2 := by
    have h := sparseRowSeed_integer_cosineMoment_eq_product w
      ((j : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / ‖v‖)
    convert h using 1
    · congr 1
      funext seed
      congr 1
      dsimp [phase, v]
      ring
    · apply Finset.prod_congr rfl
      intro i _
      congr 2
      ring
  have hmomentNonnegative (j : ℕ) :
      0 ≤ ∫ seed, Real.cos ((j : ℝ) * phase seed) ∂p.toMeasure := by
    rw [hmoment]
    positivity
  have hmomentOne :
      (∫ seed, Real.cos ((1 : ℝ) * phase seed) ∂p.toMeasure) <
        (5401 / 10000 : ℝ) := by
    rw [show (∫ seed, Real.cos ((1 : ℝ) * phase seed) ∂p.toMeasure) =
        ∏ i, Real.cos
          ((1 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
            (w i : ℝ) / ‖v‖) ^ 2 by simpa using hmoment 1]
    have heq : (∏ i, Real.cos
        ((1 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
          (w i : ℝ) / ‖v‖) ^ 2) =
        ∏ i, Real.cos ((111 * Real.sqrt 2 / 200 : ℝ) * v i / ‖v‖) ^ 2 := by
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
      (∫ seed, Real.cos ((2 : ℝ) * phase seed) ∂p.toMeasure) <
        (851 / 10000 : ℝ) := by
    rw [show (∫ seed, Real.cos ((2 : ℝ) * phase seed) ∂p.toMeasure) =
        ∏ i, Real.cos
          ((2 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
            (w i : ℝ) / ‖v‖) ^ 2 by simpa using hmoment 2]
    have heq : (∏ i, Real.cos
        ((2 : ℝ) * (111 / 100 : ℝ) * Real.sqrt 2 / 2 *
          (w i : ℝ) / ‖v‖) ^ 2) =
        ∏ i, Real.cos ((111 * Real.sqrt 2 / 100 : ℝ) * v i / ‖v‖) ^ 2 := by
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
      (∫ seed, TrigonometricBernstein.rationalCosineValue
          TernaryLInfTwoDecimal.Cap42Central.fourier (phase seed) ∂p.toMeasure) ≤
        (TernaryLInfTwoDecimal.Cap42Central.expectationBound : ℝ) := by
    apply TrigonometricBernstein.integral_rationalCosineValue_le_of_centralContract
      p.toMeasure phase hcentral.contractProof
    · intro j
      exact integrable_of_finitePMF p _
    · simp
    · exact hmomentNonnegative
    · norm_num [TernaryLInfTwoDecimal.Cap42Central.phiOneBound]
        at hmomentOne ⊢
      exact hmomentOne.le
    · norm_num [TernaryLInfTwoDecimal.Cap42Central.phiTwoBound]
        at hmomentTwo ⊢
      exact hmomentTwo.le
  rw [heventMap]
  exact hprobSeed.trans hintegral

theorem wrap_implies_tail_six_lt
    {q d inputThreshold : ℕ} {w : Fin d → ℤ}
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) (hs : Small q w)
    {row : Fin d → ℤ} (hr : WrapRow q inputThreshold w row) :
    (6 : ℝ) <
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
  have hsR : (2000 : ℝ) ^ 2 * (sqNorm w : ℝ) <
      (929 : ℝ) ^ 2 * q ^ 2 := by
    exact_mod_cast hs
  have hqNorm : (2000 : ℝ) * ‖v‖ < 929 * q := by
    rw [← hnormSq] at hsR
    nlinarith [norm_nonneg v]
  have hrR : (50 : ℝ) * q ≤ 21 * inputThreshold +
      50 * |((∑ i, row i * w i : ℤ) : ℝ)| := by
    unfold WrapRow at hr
    have hcast : ((50 * q : ℕ) : ℝ) ≤
        ((21 * inputThreshold + 50 * (∑ i, row i * w i).natAbs : ℕ) : ℝ) := by
      exact_mod_cast hr
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_natAbs, Int.cast_abs] using hcast
  have hratio : (80491 : ℝ) * ‖v‖ <
      46450 * |((∑ i, row i * w i : ℤ) : ℝ)| := by
    nlinarith
  let Y : ℝ := Real.sqrt 2 * euclideanRowDot row v / ‖v‖
  have hY : (80491 * Real.sqrt 2 / 46450 : ℝ) < |Y| := by
    dsimp [Y]
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2),
      abs_of_pos hnpos, euclideanRowDot_integerEuclideanVector]
    apply (lt_div_iff₀ hnpos).2
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hconstant : (80491 * Real.sqrt 2 / 46450 : ℝ) ^ 2 =
      6478801081 / 1078801250 := by
    rw [div_pow, mul_pow, hsqrt]
    norm_num
  have hsq : (80491 * Real.sqrt 2 / 46450 : ℝ) ^ 2 < |Y| ^ 2 :=
    pow_lt_pow_left₀ hY (by positivity) (by norm_num)
  rw [hconstant, sq_abs] at hsq
  change (6 : ℝ) <
    (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2
  norm_num at hsq ⊢
  exact lt_trans (by norm_num : (6 : ℝ) < 6478801081 / 1078801250) hsq

theorem wrap_row_probability_toReal_le
    {q d inputThreshold : ℕ} (w : Fin d → ℤ)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) (hs : Small q w) :
    (eventProbability (sparseRademacherRow d)
      (WrapRow q inputThreshold w)).toReal ≤
        97154081 / 1788800000 := by
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
        (fun row => (6 : ℝ) ≤
          (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2) :=
    eventProbability_mono (sparseRademacherRow d)
      (fun row (hr : WrapRow q inputThreshold w row) =>
        (wrap_implies_tail_six_lt hpositive hnorm hs hr).le)
  have heq : eventProbability (sparseRademacherRow d)
        (fun row => (6 : ℝ) ≤
          (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2) =
      eventProbability (rademacherPMF (Fin d × Fin 2))
        (fun bits => (6 : ℝ) ≤
          (rademacherSum (normalizedDuplicatedCoefficient v) bits) ^ 2) := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    calc
      eventProbability ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRow)
          (fun row => (6 : ℝ) ≤
            (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2) =
        eventProbability
          ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRowSeedSigns)
          (fun bits => (6 : ℝ) ≤
            (rademacherSum (normalizedDuplicatedCoefficient v) bits) ^ 2) := by
          apply eventProbability_map_congr
          intro seed
          rw [rademacherSum_normalizedDuplicatedCoefficient seed v hv]
      _ = _ := by
        rw [map_uniformSparseSeed_signs]
        unfold rademacherPMF
        rw [uniformPiPMF_eq_uniformOfFintype]
  have htail := rademacherSum_normalized_tail_six_toReal_le_fintype
    (normalizedDuplicatedCoefficient v)
    (sum_sq_normalizedDuplicatedCoefficient v hv)
  have hre := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmono
  change (eventProbability (sparseRademacherRow d)
      (WrapRow q inputThreshold w)).toReal ≤
    (eventProbability (sparseRademacherRow d)
      (fun row => (6 : ℝ) ≤
        (Real.sqrt 2 * euclideanRowDot row v / ‖v‖) ^ 2)).toReal at hre
  rw [heq] at hre
  exact hre.trans htail

theorem small_row_probability_toReal_lt
    {q d inputThreshold : ℕ} (w : Fin d → ℤ)
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w) (hs : Small q w) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal < 13939 / 20000 := by
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
    _ ≤ (TernaryLInfTwoDecimal.Cap42Central.expectationBound : ℝ) +
        97154081 / 1788800000 := add_le_add hc ht
    _ < 13939 / 20000 := by
      norm_num [TernaryLInfTwoDecimal.Cap42Central.expectationBound]

/-- The generated degree-73 diffuse cosine polynomial gives the selected
one-row bound on the entire centered cyclic arc. -/
theorem diffuseArc_row_probability_toReal_lt {q d : ℕ}
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate)
    (w : Fin d → ℤ) (hqpos : 0 < q) (hd : Diffuse q w) :
    (eventProbability (sparseRademacherRow d) (DiffuseArcRow q w)).toReal <
      13939 / 20000 := by
  classical
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  let p : PMF (SparseRowSeed d) := PMF.uniformOfFintype (SparseRowSeed d)
  let phase : SparseRowSeed d → ℝ := fun seed =>
    (2 * Real.pi / (q : ℝ)) *
      euclideanRowDot (sparseRow seed) (integerEuclideanVector w)
  let event : SparseRowSeed d → Prop :=
    fun seed => DiffuseArcRow q w (sparseRow seed)
  have hpoint (seed : SparseRowSeed d) :
      (if event seed then (1 : ℝ) else 0) ≤
        TrigonometricBernstein.rationalCosineValue
          TernaryLInfTwoDecimal.Cap42Diffuse.fourier (phase seed) := by
    by_cases hp : event seed
    · rw [if_pos hp]
      let z : ℤ := ∑ i, sparseRow seed i * w i
      let r : ℤ := centeredMod q z
      have hr : (100 : ℝ) * |(r : ℝ)| ≤ 21 * q := by
        unfold event DiffuseArcRow at hp
        have hc : 100 * r.natAbs ≤ 21 * q := hp
        have hc' : ((100 * r.natAbs : ℕ) : ℝ) ≤ ((21 * q : ℕ) : ℝ) := by
          exact_mod_cast hc
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_natAbs, Int.cast_abs]
          using hc'
      have habs : |(2 * Real.pi / (q : ℝ)) * (r : ℝ)| ≤
          21 * Real.pi / 50 := by
        rw [abs_mul, abs_div,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), abs_of_pos hqr]
        have hratio : |(r : ℝ)| / (q : ℝ) ≤ 21 / 100 := by
          apply (div_le_iff₀ hqr).2
          nlinarith [hr]
        calc
          2 * Real.pi / (q : ℝ) * |(r : ℝ)| =
              (2 * Real.pi) * (|(r : ℝ)| / (q : ℝ)) := by ring
          _ ≤ (2 * Real.pi) * (21 / 100) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = 21 * Real.pi / 50 := by ring
      have hcosPhase : Real.cos (phase seed) =
          Real.cos ((2 * Real.pi / (q : ℝ)) * (r : ℝ)) := by
        dsimp [phase]
        rw [euclideanRowDot_integerEuclideanVector]
        exact cosine_twoPiOverModulus_centeredMod (Nat.ne_of_gt hqpos) z
      have hcapPi : (21 * Real.pi / 50 : ℝ) ≤ Real.pi := by
        nlinarith [Real.pi_pos]
      have hcosMono : Real.cos (21 * Real.pi / 50) ≤
          Real.cos ((2 * Real.pi / (q : ℝ)) * (r : ℝ)) := by
        calc
          Real.cos (21 * Real.pi / 50) ≤
              Real.cos |(2 * Real.pi / (q : ℝ)) * (r : ℝ)| :=
            Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hcapPi habs
          _ = Real.cos ((2 * Real.pi / (q : ℝ)) * (r : ℝ)) := Real.cos_abs _
      apply hdiffuse.cosineDominatesOne
      rw [hcosPhase]
      have hc := cos_diffuse42_lower
      norm_num at hc ⊢
      rw [show 21 * Real.pi / 50 = Real.pi * (21 / 50 : ℝ) by ring]
        at hcosMono
      exact hc.le.trans hcosMono
    · rw [if_neg hp]
      exact hdiffuse.cosineNonnegative _
  have hprobSeed := finitePMF_eventProbability_toReal_le_integral p event
    (fun seed => TrigonometricBernstein.rationalCosineValue
      TernaryLInfTwoDecimal.Cap42Diffuse.fourier (phase seed)) hpoint
  have heventMap :
      eventProbability (sparseRademacherRow d) (DiffuseArcRow q w) =
        eventProbability p event := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    unfold eventProbability
    rw [PMF.map_comp]
    rfl
  have hmoment (j : ℕ) :
      ∫ seed, Real.cos ((j : ℝ) * phase seed) ∂p.toMeasure =
        ∏ i, Real.cos
          ((j : ℝ) * Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 := by
    have h := sparseRowSeed_integer_cosineMoment_eq_product w
      ((j : ℝ) * 2 * Real.pi / (q : ℝ))
    convert h using 1
    · congr 1
      funext seed
      congr 1
      dsimp [phase]
      ring
    · apply Finset.prod_congr rfl
      intro i _
      congr 2
      ring
  have hmomentNonnegative (j : ℕ) :
      0 ≤ ∫ seed, Real.cos ((j : ℝ) * phase seed) ∂p.toMeasure := by
    rw [hmoment]
    positivity
  have hmomentOne :
      (∫ seed, Real.cos ((1 : ℝ) * phase seed) ∂p.toMeasure) <
        (119 / 1000 : ℝ) := by
    rw [show (∫ seed, Real.cos ((1 : ℝ) * phase seed) ∂p.toMeasure) =
        ∏ i, Real.cos
          ((1 : ℝ) * Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 by
      simpa using hmoment 1]
    have hfactor (i : Fin d) :
        Real.cos (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 ≤
          Real.exp (-((Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2)) := by
      apply cos_sq_le_exp_neg_sq
      have hi : (50 : ℝ) * |(w i : ℝ)| ≤ 21 * q := by
        rw [show |(w i : ℝ)| = (((w i).natAbs : ℕ) : ℝ) by simp]
        exact_mod_cast hd.2 i
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hqr]
      have hpi : 21 * Real.pi / 50 < Real.pi / 2 := by
        nlinarith [Real.pi_pos]
      apply lt_of_le_of_lt _ hpi
      apply (div_le_iff₀ hqr).2
      nlinarith [Real.pi_pos]
    have hproduct :
        (∏ i, Real.cos ((1 : ℝ) * Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2) ≤
          ∏ i, Real.exp (-((Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sq_nonneg _
      · intro i _
        simpa only [one_mul] using hfactor i
    have hsum : Real.pi ^ 2 * (929 / 2000 : ℝ) ^ 2 ≤
        ∑ i, (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2 := by
      have hdR : (929 : ℝ) ^ 2 * q ^ 2 ≤
          (2000 : ℝ) ^ 2 * (sqNorm w : ℝ) := by
        exact_mod_cast hd.1
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
    calc
      _ ≤ ∏ i, Real.exp
          (-((Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2)) := hproduct
      _ = Real.exp (-∑ i,
          (Real.pi * (w i : ℝ) / (q : ℝ)) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_neg_distrib]
      _ ≤ Real.exp (-(Real.pi ^ 2 * (929 / 2000 : ℝ) ^ 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ < 119 / 1000 := exp_neg_diffuse42_lt
  have hintegral :
      (∫ seed, TrigonometricBernstein.rationalCosineValue
          TernaryLInfTwoDecimal.Cap42Diffuse.fourier (phase seed) ∂p.toMeasure) ≤
        (TernaryLInfTwoDecimal.Cap42Diffuse.expectationBound : ℝ) := by
    apply TrigonometricBernstein.integral_rationalCosineValue_le_of_diffuseContract
      p.toMeasure phase hdiffuse.contractProof
    · intro j
      exact integrable_of_finitePMF p _
    · simp
    · exact hmomentNonnegative
    · norm_num [TernaryLInfTwoDecimal.Cap42Diffuse.diffuseMomentBound]
        at hmomentOne ⊢
      exact hmomentOne.le
  rw [heventMap]
  exact hprobSeed.trans hintegral |>.trans_lt (by
    norm_num [TernaryLInfTwoDecimal.Cap42Diffuse.expectationBound])

theorem diffuse_row_probability_toReal_lt
    {q d inputThreshold : ℕ} (w : Fin d → ℤ) (hqpos : 0 < q)
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate)
    (hmargin : 2 * inputThreshold ≤ q) (hd : Diffuse q w) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal < 13939 / 20000 := by
  have hmono : eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w) ≤
      eventProbability (sparseRademacherRow d) (DiffuseArcRow q w) := by
    apply eventProbability_mono
    intro row hp
    unfold RowPass at hp
    unfold DiffuseArcRow
    nlinarith [sq_nonneg
      (50 * ((centeredMod q (∑ i, row i * w i)).natAbs : ℤ) -
        21 * (inputThreshold : ℤ))]
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
        (fun bits => 2500 *
          (centeredMod q (shift + sparseBit bits * w i)).natAbs ^ 2 ≤
            441 * inputThreshold ^ 2) := by
    apply eventProbability_map_congr
    intro selected
    unfold RowPass
    rw [sparseRow_join_singleton_dot]
  rw [hevent, map_uniformSparseRowSingletonSeed]
  have hpull :
      eventProbability (PMF.uniformOfFintype (Bool × Bool))
          (fun bits => 2500 *
            (centeredMod q (shift + sparseBit bits * w i)).natAbs ^ 2 ≤
              441 * inputThreshold ^ 2) =
        eventProbability sparseEntryPMF
          (fun x => 2500 *
            (centeredMod q (shift + x * w i)).natAbs ^ 2 ≤
              441 * inputThreshold ^ 2) := by
    unfold sparseEntryPMF eventProbability
    rw [PMF.map_comp]
    rfl
  rw [hpull]
  have hmono : eventProbability sparseEntryPMF
      (fun x => 2500 *
        (centeredMod q (shift + x * w i)).natAbs ^ 2 ≤
          441 * inputThreshold ^ 2) ≤
      eventProbability sparseEntryPMF
        (fun x => ScaledCenteredArcPass q 50 (21 * inputThreshold)
          (shift + x * w i)) := by
    apply eventProbability_mono
    intro x hx
    unfold ScaledCenteredArcPass
    nlinarith [sq_nonneg
      (50 * ((centeredMod q (shift + x * w i)).natAbs : ℤ) -
        21 * (inputThreshold : ℤ))]
  apply (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmono).trans
  apply sparseEntry_scaledCenteredArcPass_toReal_le_half_of_centered
    (q := q) (scale := 50) (radius := 21 * inputThreshold) shift (w i)
    (coordinate_half_modulus_of_centeredInput hcentered i)
  omega

/-- The three geometric regimes give a uniform one-row bound at the public
threshold. -/
theorem row_probability_toReal_lt
    {q d inputThreshold : ℕ} (w : Fin d → ℤ)
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate)
    (hpositive : 0 < inputThreshold) (hcentered : CenteredInput q w)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hmargin : 2 * inputThreshold ≤ q) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal < 13939 / 20000 := by
  have hqpos : 0 < q := by omega
  rcases regime_trichotomy q w with hs | hl | hd
  · exact small_row_probability_toReal_lt w hcentral hpositive hnorm hs
  · exact (large_row_probability_toReal_le_half w hcentered hmargin hl).trans_lt
      (by norm_num)
  · exact diffuse_row_probability_toReal_lt w hqpos hdiffuse hmargin hd

theorem rows_probability_lt_of_pow_bound
    {rows q d inputThreshold : ℕ} {budget : ENNReal}
    (w : Fin d → ℤ) (hpositive : 0 < inputThreshold)
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate)
    (hcentered : CenteredInput q w)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hmargin : 2 * inputThreshold ≤ q)
    (hpow : ((13939 : ENNReal) / 20000) ^ rows < budget) :
    eventProbability (sparseRademacherMatrix rows d)
      (Pass q inputThreshold w) < budget := by
  change eventProbability (sparseRademacherMatrix rows d)
    (fun J => ∀ j, RowPass q inputThreshold w (J j)) < budget
  apply (sparseRademacherMatrix_eventProbability_allRows_le_pow
    rows d (RowPass q inputThreshold w) ((13939 : ENNReal) / 20000) ?_).trans_lt
    hpow
  apply finitePMF_eventProbability_le_of_toReal_le
    (sparseRademacherRow d) (RowPass q inputThreshold w) (by finiteness)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using
    (row_probability_toReal_lt w hcentral hdiffuse hpositive hcentered
      hnorm hmargin).le

set_option exponentiation.threshold 2048 in
theorem rowBound_pow_rows256_bits133 :
    ((13939 : ENNReal) / 20000) ^ 256 < failureTarget 133 := by
  rw [← ENNReal.toReal_lt_toReal (by finiteness)
    (by unfold failureTarget; finiteness)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    failureTarget, ENNReal.toReal_inv]
  norm_num [zpow_neg]

set_option exponentiation.threshold 2048 in
theorem rowBound_pow_rows384_bits200 :
    ((13939 : ENNReal) / 20000) ^ 384 < failureTarget 200 := by
  rw [← ENNReal.toReal_lt_toReal (by finiteness)
    (by unfold failureTarget; finiteness)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    failureTarget, ENNReal.toReal_inv]
  norm_num [zpow_neg]

set_option exponentiation.threshold 2048 in
theorem rowBound_pow_rows512_bits266 :
    ((13939 : ENNReal) / 20000) ^ 512 < failureTarget 266 := by
  rw [← ENNReal.toReal_lt_toReal (by finiteness)
    (by unfold failureTarget; finiteness)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    failureTarget, ENNReal.toReal_inv]
  norm_num [zpow_neg]

theorem ternaryLInfThresholdLower21Over50_of_pow_bound
    (rows bits : ℕ)
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate)
    (hpow : ((13939 : ENNReal) / 20000) ^ rows < failureTarget bits) :
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

theorem ternaryLInfThresholdLower21Over50_rows256_bits133_of_certificates
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate) :
    LInfThresholdLowerTailAt (parametersAt 256) (failureTarget 133) :=
  ternaryLInfThresholdLower21Over50_of_pow_bound 256 133 hcentral hdiffuse
    rowBound_pow_rows256_bits133

theorem ternaryLInfThresholdLower21Over50_rows384_bits200_of_certificates
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate) :
    LInfThresholdLowerTailAt (parametersAt 384) (failureTarget 200) :=
  ternaryLInfThresholdLower21Over50_of_pow_bound 384 200 hcentral hdiffuse
    rowBound_pow_rows384_bits200

theorem ternaryLInfThresholdLower21Over50_rows512_bits266_of_certificates
    (hcentral : TernaryLInfTwoDecimal.Cap42CentralCertificate)
    (hdiffuse : TernaryLInfTwoDecimal.Cap42DiffuseCertificate) :
    LInfThresholdLowerTailAt (parametersAt 512) (failureTarget 266) :=
  ternaryLInfThresholdLower21Over50_of_pow_bound 512 266 hcentral hdiffuse
    rowBound_pow_rows512_bits266

end CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal
