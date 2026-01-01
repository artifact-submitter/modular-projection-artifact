/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Data.Nat.Choose.Central
import CertifiedJL.Analysis.SmoothBounds.LogBounds

/-!
# Explicit local bounds for centered binomial probabilities

The sparse all-ones counterexample writes one row as half the sum of `2d`
independent signs.  This file develops the coefficient comparison needed to
lower-bound its lattice probabilities by Gaussian cell masses.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- Probability of the central value in a centered `Binomial(2d, 1/2)`. -/
noncomputable def centralBinomialMass (d : ℕ) : ℝ :=
  Nat.centralBinom d / 4 ^ d

/-- Lattice mass `choose (2d, d+k) / 4^d` at nonnegative offset `k`. -/
noncomputable def centeredBinomialMassAt (d k : ℕ) : ℝ :=
  Nat.choose (2 * d) (d + k) / 4 ^ d

@[simp]
theorem centeredBinomialMassAt_zero (d : ℕ) :
    centeredBinomialMassAt d 0 = centralBinomialMass d := by
  simp [centeredBinomialMassAt, centralBinomialMass,
    Nat.centralBinom_eq_two_mul_choose]

theorem centeredBinomialMassAt_pos {d k : ℕ} (hk : k ≤ d) :
    0 < centeredBinomialMassAt d k := by
  exact div_pos (by
    exact_mod_cast Nat.choose_pos (by omega : d + k ≤ 2 * d))
    (by positivity)

theorem centralBinomialMass_pos (d : ℕ) :
    0 < centralBinomialMass d := by
  exact div_pos (by
    exact_mod_cast Nat.centralBinom_pos d) (by positivity)

/-- Exact adjacent-mass recurrence for a centered binomial law. -/
theorem centeredBinomialMassAt_succ {d k : ℕ} (hk : k < d) :
    centeredBinomialMassAt d (k + 1) =
      centeredBinomialMassAt d k *
        ((d - k : ℕ) : ℝ) / (d + k + 1) := by
  have hchoose := Nat.choose_succ_right_eq (2 * d) (d + k)
  have hsub : 2 * d - (d + k) = d - k := by omega
  rw [hsub] at hchoose
  unfold centeredBinomialMassAt
  rw [show d + (k + 1) = d + k + 1 by omega]
  field_simp
  exact_mod_cast hchoose

/--
The uniform one-step logarithmic error used in the local limit comparison.
The deliberately simple `K³` majorant avoids carrying Faulhaber identities
through the later concrete proof.
-/
noncomputable def binomialLogStepError (d K : ℕ) : ℝ :=
  ((K : ℝ) / d) ^ 3 / (1 - (K : ℝ) / d) +
    ((K : ℝ) / d) ^ 3 / 3

/--
One adjacent centered-binomial ratio is bounded by its Gaussian logarithm,
with a uniform cubic error valid for every `k < K < d`.
-/
theorem log_centeredBinomial_ratio_lower {d K k : ℕ}
    (hk : k < K) (hKd : K < d) :
    -(((2 * k + 1 : ℕ) : ℝ) / d) -
        binomialLogStepError d K ≤
      Real.log
        (((d - k : ℕ) : ℝ) / (d + k + 1)) := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hKd
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk.le
  have hk1K : ((k + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hk
  have hKlt : (K : ℝ) / d < 1 := by
    rw [div_lt_one hd]
    exact_mod_cast hKd
  have hklt : (k : ℝ) / d < 1 :=
    (div_le_div_of_nonneg_right hkK (Nat.cast_nonneg d)).trans_lt hKlt
  have hnonnegK : 0 ≤ (K : ℝ) / d := by positivity
  have hnonnegk : 0 ≤ (k : ℝ) / d := by positivity
  have hnonnegk1 : 0 ≤ ((k + 1 : ℕ) : ℝ) / d := by positivity
  have hnum :=
    neg_add_sq_add_log_one_sub_le hnonnegk hklt
  have hden := log_one_add_le_cubic hnonnegk1
  have hcubicNum :
      (((k : ℝ) / d) ^ 3 /
          (1 - (k : ℝ) / d)) ≤
        ((K : ℝ) / d) ^ 3 /
          (1 - (K : ℝ) / d) := by
    apply div_le_div₀
    · exact pow_nonneg hnonnegK 3
    · exact pow_le_pow_left₀ hnonnegk
        (div_le_div_of_nonneg_right hkK (Nat.cast_nonneg d)) 3
    · linarith
    · exact sub_le_sub_left
        (div_le_div_of_nonneg_right hkK (Nat.cast_nonneg d)) 1
  have hcubicDen :
      (((k + 1 : ℕ) : ℝ) / d) ^ 3 / 3 ≤
        ((K : ℝ) / d) ^ 3 / 3 := by
    gcongr
  have hrewrite :
      (((d - k : ℕ) : ℝ) / (d + k + 1)) =
        (1 - (k : ℝ) / d) /
          (1 + ((k + 1 : ℕ) : ℝ) / d) := by
    rw [Nat.cast_sub (R := ℝ) (show k ≤ d by omega)]
    push_cast
    field_simp [hd.ne']
    ring
  rw [hrewrite, Real.log_div (by linarith) (by positivity)]
  unfold binomialLogStepError
  have hquad :
      0 ≤ (((k + 1 : ℕ) : ℝ) / d) ^ 2 -
        ((k : ℝ) / d) ^ 2 := by
    exact sub_nonneg.mpr <| pow_le_pow_left₀ hnonnegk
      (div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.le_succ k) (Nat.cast_nonneg d)) 2
  have hlinear :
      (k : ℝ) / d + ((k + 1 : ℕ) : ℝ) / d =
        ((2 * k + 1 : ℕ) : ℝ) / d := by
    push_cast
    ring
  linarith

/--
Accumulated local logarithmic comparison out to offset `k`.

The proof is an induction over adjacent binomial coefficients.  This keeps
the exact telescoping term `k²/d` explicit and charges the same cubic error
at each of at most `K` steps.
-/
theorem log_centeredBinomialMassAt_lower {d K k : ℕ}
    (hk : k ≤ K) (hKd : K < d) :
    Real.log (centralBinomialMass d) -
        (k : ℝ) ^ 2 / d -
        (k : ℝ) * binomialLogStepError d K ≤
      Real.log (centeredBinomialMassAt d k) := by
  induction k with
  | zero =>
      simp [centeredBinomialMassAt_zero]
  | succ k ih =>
      have hkK : k < K := Nat.lt_of_succ_le hk
      have hkd : k < d := hkK.trans hKd
      have hmass : 0 < centeredBinomialMassAt d k :=
        centeredBinomialMassAt_pos hkd.le
      have hratio :
          0 < (((d - k : ℕ) : ℝ) / (d + k + 1)) := by
        exact div_pos (by exact_mod_cast Nat.sub_pos_of_lt hkd)
          (by positivity)
      have hstep :=
        log_centeredBinomial_ratio_lower hkK hKd
      have hih := ih hkK.le
      have hd : (d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hKd))
      rw [centeredBinomialMassAt_succ hkd]
      rw [show
          centeredBinomialMassAt d k * ((d - k : ℕ) : ℝ) /
              (d + k + 1) =
            centeredBinomialMassAt d k *
              (((d - k : ℕ) : ℝ) / (d + k + 1)) by ring,
        Real.log_mul hmass.ne' hratio.ne']
      calc
        Real.log (centralBinomialMass d) -
              ((k + 1 : ℕ) : ℝ) ^ 2 / d -
              ((k + 1 : ℕ) : ℝ) * binomialLogStepError d K =
            (Real.log (centralBinomialMass d) -
                (k : ℝ) ^ 2 / d -
                (k : ℝ) * binomialLogStepError d K) +
              (-(((2 * k + 1 : ℕ) : ℝ) / d) -
                binomialLogStepError d K) := by
          push_cast
          field_simp [hd]
          ring
        _ ≤ Real.log (centeredBinomialMassAt d k) +
              Real.log
                (((d - k : ℕ) : ℝ) / (d + k + 1)) :=
          add_le_add hih hstep

/-- Exponential form of `log_centeredBinomialMassAt_lower`. -/
theorem centeredBinomialMassAt_lower {d K k : ℕ}
    (hk : k ≤ K) (hKd : K < d) :
    centralBinomialMass d *
        Real.exp
          (-((k : ℝ) ^ 2 / d +
            (k : ℝ) * binomialLogStepError d K)) ≤
      centeredBinomialMassAt d k := by
  have hlog := log_centeredBinomialMassAt_lower hk hKd
  have hcentral := centralBinomialMass_pos d
  have hmass := centeredBinomialMassAt_pos (hk.trans hKd.le)
  have hexp := (Real.exp_le_exp).2 hlog
  rw [show
      Real.log (centralBinomialMass d) -
          (k : ℝ) ^ 2 / d -
          (k : ℝ) * binomialLogStepError d K =
        Real.log (centralBinomialMass d) +
          -((k : ℝ) ^ 2 / d +
            (k : ℝ) * binomialLogStepError d K) by ring,
    Real.exp_add, Real.exp_log hcentral,
    Real.exp_log hmass] at hexp
  exact hexp

/-- The central binomial coefficient as a real factorial quotient. -/
theorem centralBinom_cast_eq_factorial_ratio (d : ℕ) :
    (Nat.centralBinom d : ℝ) =
      (2 * d).factorial / d.factorial ^ 2 := by
  have hnat :=
    Nat.choose_mul_factorial_mul_factorial
      (n := 2 * d) (k := d) (by omega)
  rw [Nat.centralBinom_eq_two_mul_choose] at *
  rw [show 2 * d - d = d by omega] at hnat
  have hreal :
      (Nat.choose (2 * d) d : ℝ) * d.factorial * d.factorial =
        ((2 * d).factorial : ℝ) := by
    exact_mod_cast hnat
  rw [eq_div_iff (by positivity)]
  nlinarith

/-- Wallis's finite product is the reciprocal central-mass square factor. -/
theorem wallis_eq_centralBinomialMass (d : ℕ) :
    Real.Wallis.W d =
      1 / (centralBinomialMass d ^ 2 * (2 * d + 1)) := by
  rw [Real.Wallis.W_eq_factorial_ratio,
    centralBinomialMass, centralBinom_cast_eq_factorial_ratio]
  field_simp
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  omega

/--
The Wallis lower bound for the central lattice mass, in the normalization
whose Gaussian density is `π⁻¹/² exp(-x²)`.
-/
theorem centralBinomialMass_sq_lower (d : ℕ) :
    1 / (Real.pi * (d + 1 / 2 : ℝ)) ≤
      centralBinomialMass d ^ 2 := by
  have hwallis := Real.Wallis.W_le d
  rw [wallis_eq_centralBinomialMass] at hwallis
  have hp := centralBinomialMass_pos d
  have hfactor : 0 < (2 * d + 1 : ℝ) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_le_iff₀ (mul_pos (sq_pos_of_pos hp) hfactor)] at hwallis
  rw [div_le_iff₀ (mul_pos hpi (by positivity))]
  convert hwallis using 1
  ring

/--
A convenient exponential form of the central Wallis estimate.

The loss `exp (-1/d)` is intentionally a little looser than the paper's
`exp (-1/(4d))`; at the concrete dimension it changes the final loss by less
than `10⁻⁷` and substantially shortens the reusable argument.
-/
theorem centralBinomialMass_exp_lower {d : ℕ} (hdNat : 0 < d) :
    Real.exp (-(1 : ℝ) / d) /
        (Real.sqrt Real.pi * Real.sqrt d) ≤
      centralBinomialMass d := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtPi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have hsqrtD : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd
  have hsmall :
      0 ≤ Real.exp (-(1 : ℝ) / d) /
        (Real.sqrt Real.pi * Real.sqrt d) := by positivity
  have hmass : 0 ≤ centralBinomialMass d :=
    (centralBinomialMass_pos d).le
  rw [← sq_le_sq₀ hsmall hmass]
  calc
    (Real.exp (-(1 : ℝ) / d) /
        (Real.sqrt Real.pi * Real.sqrt d)) ^ 2 =
        Real.exp (-(2 : ℝ) / d) /
          (Real.pi * d) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hpi.le,
        Real.sq_sqrt hd.le, pow_two, ← Real.exp_add]
      congr 2
      field_simp
      ring
    _ ≤ 1 / (Real.pi * (d + 1 / 2 : ℝ)) := by
      have hexpLower :
          (1 + (1 : ℝ) / (2 * d)) ≤
            Real.exp ((2 : ℝ) / d) := by
        calc
          1 + (1 : ℝ) / (2 * d) ≤
              (2 : ℝ) / d + 1 := by
            field_simp
            nlinarith
          _ ≤ Real.exp ((2 : ℝ) / d) :=
            Real.add_one_le_exp _
      have hInv :
          Real.exp (-(2 : ℝ) / d) ≤
            d / (d + 1 / 2 : ℝ) := by
        rw [show -(2 : ℝ) / d = -((2 : ℝ) / d) by ring,
          Real.exp_neg]
        have hden : 0 < 1 + (1 : ℝ) / (2 * d) := by positivity
        have hInv' :
            (Real.exp ((2 : ℝ) / d))⁻¹ ≤
              (1 + (1 : ℝ) / (2 * d))⁻¹ :=
          (inv_le_inv₀ (Real.exp_pos _) hden).2 hexpLower
        calc
          (Real.exp ((2 : ℝ) / d))⁻¹ ≤
              (1 + (1 : ℝ) / (2 * d))⁻¹ := hInv'
          _ = d / (d + 1 / 2 : ℝ) := by
            field_simp
      rw [div_le_div_iff₀ (mul_pos hpi hd)
        (mul_pos hpi (by positivity))]
      calc
        Real.exp (-(2 : ℝ) / d) *
              (Real.pi * (d + 1 / 2 : ℝ)) ≤
            (d / (d + 1 / 2 : ℝ)) *
              (Real.pi * (d + 1 / 2 : ℝ)) := by
          gcongr
        _ = 1 * (Real.pi * d) := by
          field_simp
    _ ≤ centralBinomialMass d ^ 2 :=
      centralBinomialMass_sq_lower d

end Probability
end CertifiedJL
