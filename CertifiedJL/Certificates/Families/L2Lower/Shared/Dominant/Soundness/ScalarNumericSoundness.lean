/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExp
import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Arithmetic.Transcendental.SquareRoot.Sqrt
import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ScalarNumeric
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Cell

/-!
# Soundness of shared dominant-coordinate interval arithmetic
-/

namespace CertifiedJL
namespace DominantNumeric

/-- Exact rational literals are enclosed by their executable intervals. -/
theorem contains_rat (q : ℚ) : (rat q).Contains (q : ℝ) :=
  Interval.contains_ofRat precision q

/-- Division is sound when the executable denominator interval is positive. -/
theorem contains_div {I J : DInterval} {x y : ℝ}
    (hJ : 0 < J.lo) (hx : I.Contains x) (hy : J.Contains y) :
    (div I J).Contains (x / y) := by
  unfold div
  simpa [div_eq_mul_inv] using
    Interval.contains_mul hx (Interval.contains_reciprocal_of_pos hJ hy)

private theorem toReal_min (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (min a b) =
      min (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  unfold Dyadic.toReal
  rw [Int.cast_min, min_div_div_right]
  positivity

private theorem toReal_max (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (max a b) =
      max (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  unfold Dyadic.toReal
  rw [Int.cast_max, max_div_div_right]
  positivity

theorem contains_minInterval {I J : DInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (minInterval I J).Contains (min x y) := by
  unfold minInterval Interval.Contains at *
  constructor
  · rw [toReal_min]
    exact min_le_min hx.1 hy.1
  · rw [toReal_min]
    exact min_le_min hx.2 hy.2

theorem contains_maxInterval {I J : DInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (maxInterval I J).Contains (max x y) := by
  unfold maxInterval Interval.Contains at *
  constructor
  · rw [toReal_max]
    exact max_le_max hx.1 hy.1
  · rw [toReal_max]
    exact max_le_max hx.2 hy.2

private theorem contains_npowBinRec_go (k : ℕ)
    {A B : DInterval} {a b : ℝ}
    (hA : A.Contains a) (hB : B.Contains b) :
    (npowBinRec.go k A B).Contains (a * b ^ k) := by
  induction k using Nat.binaryRec generalizing A B a b with
  | zero => simpa [npowBinRec.go] using hA
  | bit bit n ih =>
      rw [npowBinRec.go, Nat.binaryRec_eq _ _ (Or.inl rfl)]
      cases bit
      · change (npowBinRec.go n A (B * B)).Contains
          (a * b ^ Nat.bit false n)
        simpa [Nat.bit_false, pow_mul, pow_two] using
          ih hA (Interval.contains_mul hB hB)
      · change (npowBinRec.go n (A * B) (B * B)).Contains
          (a * b ^ Nat.bit true n)
        convert ih (Interval.contains_mul hA hB)
          (Interval.contains_mul hB hB) using 1
        rw [Nat.bit_true, pow_succ, pow_mul, pow_two]
        ring

/-- Binary interval powers enclose the corresponding real natural power. -/
theorem contains_powNat {I : DInterval} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (powNat I n).Contains (x ^ n) := by
  change (npowBinRec.go n (rat 1) I).Contains (x ^ n)
  simpa using contains_npowBinRec_go n (contains_rat 1) hx

/-- The configured exponential evaluator is sound for exponents bounded by one. -/
theorem contains_expUpper {I : DInterval} {x : ℝ}
    (hx : I.Contains x) (hupper : I.upperRat ≤ 1) :
    (expUpper I).Contains (Real.exp x) := by
  apply DyadicExp.ofIntervalUpper_contains_of_upperRat_le_one
  · norm_num [precision, Dyadic.scale]
  · norm_num [expSquarings]
  · exact hx
  · exact hupper

/-- The executable six-decimal interval encloses the real value of `π`. -/
theorem contains_piInterval : piInterval.Contains Real.pi := by
  apply Interval.contains_enclose
  constructor
  · norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have h := pi_gt_3141592_div_1000000
    norm_num at h
    exact h.le
  · norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have h := pi_lt_3141593_div_1000000
    norm_num at h
    exact h.le

/-- The exact rational residual maximum casts to the shared real expression. -/
theorem hSqRat_cast (lower upper z : ℚ) :
    (hSqRat lower upper z : ℝ) = dominantCellHsq lower upper z := by
  by_cases hcritical : z * lower ≤ 1 ∧ 1 ≤ z * upper
  · simp [hSqRat, dominantCellHsq, hcritical]
  · simp [hSqRat, dominantCellHsq, hcritical]

/-- The exact rational row correction casts to the shared real correction. -/
theorem rhoRat_cast (lower upper z : ℚ) :
    (rhoRat lower upper z : ℝ) = dominantCellRho lower upper z := by
  simp only [rhoRat, dominantCellRho, Rat.cast_min, Rat.cast_max,
    Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Rat.cast_add, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero, hSqRat_cast]

/-- Distributing one exponential equally across `k` active factors is exact. -/
theorem exp_mul_pow_eq_pow_exp_div_mul (x active inactive : ℝ) (k total : ℕ)
    (hk : 0 < k) :
    Real.exp x * active ^ k * inactive ^ (total - k) =
      (Real.exp (x / k) * active) ^ k * inactive ^ (total - k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  field_simp

end DominantNumeric
end CertifiedJL
