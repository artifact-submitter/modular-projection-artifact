import CertifiedJL.Arithmetic.Transcendental.Exponential.TaylorExpData
import CertifiedJL.Arithmetic.Transcendental.Exponential.Exp

namespace CertifiedJL.TaylorExp

private noncomputable def p4 (t : ℝ) : ℝ :=
  1 + t * (1 + t * (1 / 2 + t * (1 / 6 + t * (1 / 24))))

private theorem p4_ge_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ p4 t := by
  dsimp [p4]
  exact le_add_of_nonneg_right (by positivity)

private theorem p4_le_exp {t : ℝ} (ht : 0 ≤ t) : p4 t ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  dsimp [p4]
  nlinarith

private theorem polynomial4_contains {p : ℕ} {I : Interval p} {t : ℝ}
    (ht : I.Contains t) : (polynomial4 p I).Contains (p4 t) := by
  unfold polynomial4 p4
  exact Interval.contains_add (by simpa using Interval.contains_ofRat p (1 : ℚ))
    (Interval.contains_mul ht
      (Interval.contains_add (by simpa using Interval.contains_ofRat p (1 : ℚ))
        (Interval.contains_mul ht
          (Interval.contains_add (by simpa using Interval.contains_ofRat p (1 / 2 : ℚ))
            (Interval.contains_mul ht
              (Interval.contains_add (by simpa using Interval.contains_ofRat p (1 / 6 : ℚ))
                (Interval.contains_mul ht
                  (by simpa using Interval.contains_ofRat p (1 / 24 : ℚ)))))))))

theorem negUpper_contains {p k : ℕ} {x : ℚ} (hx : 0 ≤ x) :
    (negUpper p x k).Contains (Real.exp (-x)) := by
  let t : ℚ := x / (2 ^ k : ℕ)
  have ht : 0 ≤ (t : ℝ) := by dsimp [t]; positivity
  have hP := polynomial4_contains (Interval.contains_ofRat p t)
  have hbase : (positiveBase p x k).Contains (p4 t) := by
    constructor
    · change Dyadic.toReal p (max (Dyadic.scale p : ℤ) _) ≤ p4 t
      unfold Dyadic.toReal
      rw [Int.cast_max, ← max_div_div_right (by positivity : (0 : ℝ) ≤ Dyadic.scale p)]
      apply max_le
      · simpa using p4_ge_one ht
      · exact hP.1
    · exact hP.2
  have hpos : 0 < (positiveBase p x k).lo :=
    lt_of_lt_of_le (by exact_mod_cast Dyadic.scale_pos p) (le_max_left _ _)
  have hr := Interval.contains_reciprocal_of_pos hpos hbase
  have he : Real.exp (-(t : ℝ)) ≤ (p4 t)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (p4_ge_one ht))).mpr
      (p4_le_exp ht)
  have hp := pow_le_pow_left₀ (Real.exp_nonneg _) he (2 ^ k)
  have hi := Interval.contains_squareN hr k
  have heq : Real.exp (-(x : ℝ)) = Real.exp (-(t : ℝ)) ^ (2 ^ k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [t]
    push_cast
    field_simp
  constructor
  · simpa [negUpper, Exp.upperHull] using Real.exp_nonneg (-(x : ℝ))
  · rw [heq]
    exact hp.trans (by simpa [negUpper, Exp.upperHull,
      Interval.iterSquare_eq_pow_two_pow] using hi.2)

private noncomputable def p5 (t : ℝ) : ℝ :=
  1 + t * (1 + t * (1 / 2 + t * (1 / 6 + t * (1 / 24 + t * (1 / 100)))))

private theorem exp_le_p5 {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t ≤ p5 t := by
  have h := Real.exp_bound' ht ht1 (n := 5) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  dsimp [p5]
  nlinarith

private theorem polynomial5Upper_contains {p : ℕ} {I : Interval p} {t : ℝ}
    (ht : I.Contains t) : (polynomial5Upper p I).Contains (p5 t) := by
  unfold polynomial5Upper p5
  exact Interval.contains_add (by simpa using Interval.contains_ofRat p (1 : ℚ))
    (Interval.contains_mul ht
      (Interval.contains_add (by simpa using Interval.contains_ofRat p (1 : ℚ))
        (Interval.contains_mul ht
          (Interval.contains_add (by simpa using Interval.contains_ofRat p (1 / 2 : ℚ))
            (Interval.contains_mul ht
              (Interval.contains_add (by simpa using Interval.contains_ofRat p (1 / 6 : ℚ))
                (Interval.contains_mul ht
                  (Interval.contains_add (by simpa using Interval.contains_ofRat p (1 / 24 : ℚ))
                    (Interval.contains_mul ht
                      (by simpa using Interval.contains_ofRat p (1 / 100 : ℚ)))))))))))

theorem posUpper_contains {p k : ℕ} {x : ℚ} (hx : 0 ≤ x)
    (hupper : x ≤ (2 ^ k : ℕ)) :
    (posUpper p x k).Contains (Real.exp x) := by
  let t : ℚ := x / (2 ^ k : ℕ)
  have ht : 0 ≤ (t : ℝ) := by dsimp [t]; positivity
  have ht1 : (t : ℝ) ≤ 1 := by
    have h : t ≤ 1 := (div_le_one (by positivity)).mpr hupper
    exact_mod_cast h
  have hP := polynomial5Upper_contains (Interval.contains_ofRat p t)
  have hp := pow_le_pow_left₀ (Real.exp_nonneg _) (exp_le_p5 ht ht1) (2 ^ k)
  have hi := Interval.contains_squareN hP k
  have heq : Real.exp (x : ℝ) = Real.exp (t : ℝ) ^ (2 ^ k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [t]
    push_cast
    field_simp
  constructor
  · simpa [posUpper, Exp.upperHull] using Real.exp_nonneg (x : ℝ)
  · rw [heq]
    exact hp.trans (by simpa [posUpper, Exp.upperHull, t,
      Interval.iterSquare_eq_pow_two_pow] using hi.2)

end CertifiedJL.TaylorExp
