import CertifiedJL.Certificates.Families.OneRow975.Finite.NatIntervalCore
import Mathlib.Algebra.Order.Floor.Div

namespace CertifiedJL
namespace SparseOneRowCertificate
namespace NatInterval

variable {p : ℕ}

/-- Re-embed a nonnegative dyadic interval into the production signed type. -/
def toInterval (I : NatInterval p) : Interval p :=
  ⟨(I.lo : ℤ), (I.hi : ℤ)⟩

/-- Real containment for a nonnegative dyadic interval. -/
def Contains (I : NatInterval p) (x : ℝ) : Prop :=
  Dyadic.toReal p (I.lo : ℤ) ≤ x ∧
    x ≤ Dyadic.toReal p (I.hi : ℤ)

theorem contains_iff_toInterval (I : NatInterval p) (x : ℝ) :
    Contains I x ↔ Interval.Contains (toInterval I) x := by
  rfl

theorem roundUp_nonneg {x : ℚ} (hx : 0 ≤ x) :
    0 ≤ Dyadic.roundUp p x := by
  have hle := Dyadic.roundUp_spec p x
  have hscale : (0 : ℚ) < (Dyadic.scale p : ℚ) := by
    exact_mod_cast Dyadic.scale_pos p
  have hraw : (0 : ℚ) ≤ Dyadic.toRat p (Dyadic.roundUp p x) := hx.trans hle
  unfold Dyadic.toRat at hraw
  have hnum : (0 : ℚ) ≤ (Dyadic.roundUp p x : ℚ) := by
    rw [div_nonneg_iff] at hraw
    rcases hraw with h | h
    · exact h.1
    · exact False.elim (by linarith [hscale, h.2])
  exact_mod_cast hnum

theorem ofRat_toInterval {x : ℚ} (hx : 0 ≤ x) :
    toInterval (ofRat p x) = Interval.ofRat p x := by
  apply congrArg₂ Interval.mk
  · exact Int.toNat_of_nonneg (Dyadic.roundDown_nonneg hx)
  · exact Int.toNat_of_nonneg (roundUp_nonneg hx)

theorem toInterval_add (I J : NatInterval p) :
    toInterval (I + J) = toInterval I + toInterval J := by
  change toInterval (NatInterval.add I J) =
    Interval.add (toInterval I) (toInterval J)
  cases I
  cases J
  simp [toInterval, NatInterval.add, Interval.add]

theorem contains_ofRat {x : ℚ} (hx : 0 ≤ x) :
    Contains (ofRat p x) x := by
  rw [contains_iff_toInterval]
  rw [ofRat_toInterval hx]
  exact Interval.contains_ofRat p x

theorem contains_add {I J : NatInterval p} {x y : ℝ}
    (hx : Contains I x) (hy : Contains J y) :
    Contains (I + J) (x + y) := by
  rw [contains_iff_toInterval] at hx hy ⊢
  exact toInterval_add I J ▸ Interval.contains_add hx hy

theorem natDiv_toReal_le (a d : ℕ) (hd : 0 < d) :
    ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)]
  exact_mod_cast Nat.div_mul_le_self a d

theorem nat_le_ceilDiv_toReal (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / d ≤ (NatInterval.ceilDiv a d : ℕ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)]
  have h : a ≤ NatInterval.ceilDiv a d * d := by
    simpa [NatInterval.ceilDiv, Nat.ceilDiv_eq_add_pred_div, Nat.mul_comm] using
      (le_smul_ceilDiv (α := ℕ) (β := ℕ) hd (b := a))
  exact_mod_cast h

theorem contains_mul {I J : NatInterval p} {x y : ℝ}
    (hx : Contains I x) (hy : Contains J y) :
    Contains (I * J) (x * y) := by
  have hscale : 0 < NatInterval.scale p := by
    exact pow_pos (by norm_num) _
  have hscaleR : (0 : ℝ) < NatInterval.scale p := by
    exact_mod_cast hscale
  have hx0 : 0 ≤ x := by
    have hlo : 0 ≤ Dyadic.toReal p (I.lo : ℤ) := by
      unfold Dyadic.toReal
      positivity
    exact hlo.trans hx.1
  have hy0 : 0 ≤ y := by
    have hlo : 0 ≤ Dyadic.toReal p (J.lo : ℤ) := by
      unfold Dyadic.toReal
      positivity
    exact hlo.trans hy.1
  have hxlo : ((I.lo : ℤ) : ℝ) / NatInterval.scale p ≤ x := by
    have h := hx.1
    change ((I.lo : ℤ) : ℝ) / (Dyadic.scale p : ℝ) ≤ x at h
    simpa [NatInterval.scale, Dyadic.scale] using h
  have hylo : ((J.lo : ℤ) : ℝ) / NatInterval.scale p ≤ y := by
    have h := hy.1
    change ((J.lo : ℤ) : ℝ) / (Dyadic.scale p : ℝ) ≤ y at h
    simpa [NatInterval.scale, Dyadic.scale] using h
  have hxhi : x ≤ ((I.hi : ℤ) : ℝ) / NatInterval.scale p := by
    have h := hx.2
    change x ≤ ((I.hi : ℤ) : ℝ) / (Dyadic.scale p : ℝ) at h
    simpa [NatInterval.scale, Dyadic.scale] using h
  have hyhi : y ≤ ((J.hi : ℤ) : ℝ) / NatInterval.scale p := by
    have h := hy.2
    change y ≤ ((J.hi : ℤ) : ℝ) / (Dyadic.scale p : ℝ) at h
    simpa [NatInterval.scale, Dyadic.scale] using h
  have hprodlo :
      Dyadic.toReal p ((I.lo * J.lo / NatInterval.scale p : ℕ) : ℤ) ≤
        x * y := by
    change ((I.lo * J.lo / NatInterval.scale p : ℕ) : ℝ) /
        NatInterval.scale p ≤ x * y
    calc
      ((I.lo * J.lo / NatInterval.scale p : ℕ) : ℝ) /
          NatInterval.scale p ≤
          ((I.lo * J.lo : ℕ) : ℝ) /
            (NatInterval.scale p : ℝ) ^ 2 := by
        calc
          ((I.lo * J.lo / NatInterval.scale p : ℕ) : ℝ) /
              NatInterval.scale p ≤
              ((I.lo * J.lo : ℕ) : ℝ) /
                NatInterval.scale p /
                  NatInterval.scale p := by
            apply div_le_div_of_nonneg_right
            · exact natDiv_toReal_le _ _ hscale
            · positivity
          _ = ((I.lo * J.lo : ℕ) : ℝ) /
              (NatInterval.scale p : ℝ) ^ 2 := by ring
      _ = (((I.lo : ℤ) : ℝ) / NatInterval.scale p) *
          (((J.lo : ℤ) : ℝ) / NatInterval.scale p) := by
        push_cast
        field_simp
      _ ≤ x * y := by
        calc
          (((I.lo : ℤ) : ℝ) / NatInterval.scale p) *
              (((J.lo : ℤ) : ℝ) / NatInterval.scale p) ≤
              x * (((J.lo : ℤ) : ℝ) / NatInterval.scale p) := by
            exact mul_le_mul_of_nonneg_right hxlo (by positivity)
          _ ≤ x * y := by
            exact mul_le_mul_of_nonneg_left hylo hx0
  have hproduphi :
      x * y ≤ Dyadic.toReal p
        ((NatInterval.ceilDiv (I.hi * J.hi)
          (NatInterval.scale p) : ℕ) : ℤ) := by
    change x * y ≤
      ((NatInterval.ceilDiv (I.hi * J.hi) (NatInterval.scale p) : ℕ) : ℝ) /
        NatInterval.scale p
    calc
      x * y ≤ (((I.hi : ℤ) : ℝ) / NatInterval.scale p) *
          (((J.hi : ℤ) : ℝ) / NatInterval.scale p) := by
        calc
          x * y ≤ (((I.hi : ℤ) : ℝ) / NatInterval.scale p) * y := by
            exact mul_le_mul_of_nonneg_right hxhi hy0
          _ ≤ (((I.hi : ℤ) : ℝ) / NatInterval.scale p) *
              (((J.hi : ℤ) : ℝ) / NatInterval.scale p) := by
            exact mul_le_mul_of_nonneg_left hyhi (by positivity)
      _ = ((I.hi * J.hi : ℕ) : ℝ) /
          (NatInterval.scale p : ℝ) ^ 2 := by
        push_cast
        field_simp
      _ ≤ ((NatInterval.ceilDiv (I.hi * J.hi)
          (NatInterval.scale p) : ℕ) : ℝ) /
          NatInterval.scale p := by
        calc
          ((I.hi * J.hi : ℕ) : ℝ) /
              (NatInterval.scale p : ℝ) ^ 2 =
              ((I.hi * J.hi : ℕ) : ℝ) /
                NatInterval.scale p /
                  NatInterval.scale p := by ring
          _ ≤ ((NatInterval.ceilDiv (I.hi * J.hi)
              (NatInterval.scale p) : ℕ) : ℝ) /
              NatInterval.scale p := by
            apply div_le_div_of_nonneg_right
            · exact nat_le_ceilDiv_toReal _ _ hscale
            · positivity
  exact ⟨hprodlo, hproduphi⟩

theorem contains_reciprocal {I : NatInterval p} {x : ℝ}
    (hx : Contains I x) (hpos : 0 < I.lo) :
    Contains I.reciprocal x⁻¹ := by
  have hscale : 0 < NatInterval.scale p := by
    exact pow_pos (by norm_num) _
  have hscaleR : (0 : ℝ) < NatInterval.scale p := by
    exact_mod_cast hscale
  have hxlo : ((I.lo : ℤ) : ℝ) / NatInterval.scale p ≤ x := by
    have h := hx.1
    change ((I.lo : ℤ) : ℝ) / (Dyadic.scale p : ℝ) ≤ x at h
    simpa [NatInterval.scale, Dyadic.scale] using h
  have hxhi : x ≤ ((I.hi : ℤ) : ℝ) / NatInterval.scale p := by
    have h := hx.2
    change x ≤ ((I.hi : ℤ) : ℝ) / (Dyadic.scale p : ℝ) at h
    simpa [NatInterval.scale, Dyadic.scale] using h
  have hlo : (0 : ℝ) < ((I.lo : ℤ) : ℝ) / NatInterval.scale p := by
    positivity
  have hhi : (0 : ℝ) < ((I.hi : ℤ) : ℝ) / NatInterval.scale p := by
    have hle := hxlo.trans hxhi
    exact hlo.trans_le hle
  have hxpos : 0 < x := hlo.trans_le hxlo
  have hvalid : I.lo ≤ I.hi := by
    have h := hxlo.trans hxhi
    have hscaled : ((I.lo : ℤ) : ℝ) ≤ ((I.hi : ℤ) : ℝ) :=
      (div_le_div_iff_of_pos_right hscaleR).mp h
    have hnat : I.lo ≤ I.hi := by exact_mod_cast hscaled
    exact hnat
  have hIhi : 0 < I.hi := lt_of_lt_of_le hpos hvalid
  let ss : ℕ := NatInterval.scale p * NatInterval.scale p
  have hss : (0 : ℝ) < ss := by
    dsimp [ss]
    exact_mod_cast (Nat.mul_pos hscale hscale)
  have hss_eq : (ss : ℝ) = (NatInterval.scale p : ℝ) ^ 2 := by
    dsimp [ss]
    push_cast
    ring
  change
    (Dyadic.toReal p
        ((NatInterval.scale p * NatInterval.scale p / I.hi : ℕ) : ℤ) ≤ x⁻¹ ∧
      x⁻¹ ≤ Dyadic.toReal p
        ((NatInterval.ceilDiv (NatInterval.scale p * NatInterval.scale p) I.lo : ℕ) : ℤ))
  constructor
  · change ((ss / I.hi : ℕ) : ℝ) / NatInterval.scale p ≤ x⁻¹
    calc
      ((ss / I.hi : ℕ) : ℝ) / NatInterval.scale p ≤
          ((ss : ℝ) / I.hi) / NatInterval.scale p := by
        apply div_le_div_of_nonneg_right
        · exact natDiv_toReal_le _ _ hIhi
        · positivity
      _ = (((I.hi : ℤ) : ℝ) / NatInterval.scale p)⁻¹ := by
        rw [hss_eq]
        push_cast
        norm_num
        field_simp
      _ ≤ x⁻¹ := (inv_le_inv₀ hhi hxpos).mpr hxhi
  · change x⁻¹ ≤ ((NatInterval.ceilDiv ss I.lo : ℕ) : ℝ) /
      NatInterval.scale p
    calc
      x⁻¹ ≤ (((I.lo : ℤ) : ℝ) / NatInterval.scale p)⁻¹ :=
        (inv_le_inv₀ hxpos hlo).mpr hxlo
      _ = ((ss : ℝ) / I.lo) / NatInterval.scale p := by
        rw [hss_eq]
        push_cast
        norm_num
        field_simp
      _ ≤ ((NatInterval.ceilDiv ss I.lo : ℕ) : ℝ) /
          NatInterval.scale p := by
        apply div_le_div_of_nonneg_right
        · exact nat_le_ceilDiv_toReal _ _ hpos
        · positivity

theorem contains_squareN {I : NatInterval p} {x : ℝ}
    (hx : Contains I x) (n : ℕ) :
    Contains (I.squareN n) (x ^ (2 ^ n)) := by
  induction n with
  | zero => simpa [NatInterval.squareN] using hx
  | succ n ih =>
      have hsq := contains_mul ih ih
      change Contains (NatInterval.square (NatInterval.squareN I n))
        (x ^ (2 ^ n * 2))
      simpa [NatInterval.square, pow_two, ← pow_add, Nat.mul_two] using hsq

private theorem exp_neg_upper_real {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n) :
    Real.exp (-x) ≤ ((1 + x / n)⁻¹) ^ n := by
  have ht : 0 ≤ x / (n : ℝ) := div_nonneg hx (by positivity)
  have hbase :
      Real.exp (-(x / n)) ≤ (1 + x / n)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr <|
      by simpa [add_comm] using Real.add_one_le_exp (x / n)
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hbase n
  calc
    Real.exp (-x) = Real.exp ((n : ℝ) * (-(x / n))) := by
      congr 1
      field_simp
    _ = Real.exp (-(x / n)) ^ n := Real.exp_nat_mul _ _
    _ ≤ ((1 + x / n)⁻¹) ^ n := hpow

private theorem exp_pos_upper_real {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hxn : x < n) :
    Real.exp x ≤ ((1 - x / n)⁻¹) ^ n := by
  have hn : 0 < n := by
    by_contra hn0
    simp only [not_lt, Nat.le_zero] at hn0
    subst n
    exact (not_lt_of_ge hx) (by simpa using hxn)
  have ht : x / (n : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hxn
  have hbase :
      Real.exp (x / n) ≤ (1 - x / n)⁻¹ := by
    calc
      Real.exp (x / n) = (Real.exp (-(x / n)))⁻¹ := by
        simpa using Real.exp_neg (-(x / n))
      _ ≤ (1 - x / n)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (sub_pos.mpr ht)).mpr <|
          by linarith [Real.add_one_le_exp (-(x / n))]
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hbase n
  calc
    Real.exp x = Real.exp ((n : ℝ) * (x / n)) := by
      congr 1
      field_simp
    _ = Real.exp (x / n) ^ n := Real.exp_nat_mul _ _
    _ ≤ ((1 - x / n)⁻¹) ^ n := hpow

theorem contains_expNegUpper {x : ℚ} (k : ℕ) (hx : 0 ≤ x) :
    Contains (NatInterval.expNegUpper p x k)
      (Real.exp (-(x : ℝ))) := by
  let arg : ℚ := x / (2 ^ k : ℕ)
  have harg0 : 0 ≤ arg := div_nonneg hx (by positivity)
  have harg := contains_ofRat (p := p) (x := arg) harg0
  have hone : Contains (ofRat p 1) (1 : ℝ) :=
    by simpa using (contains_ofRat (p := p) (x := 1) (by norm_num))
  have hsum := contains_add hone harg
  have hbasepos : 0 < (ofRat p 1 + ofRat p arg).lo := by
    have honeLo : (ofRat p 1).lo = NatInterval.scale p := by
      simp only [ofRat, Dyadic.roundDown_one]
      change Int.toNat ((2 ^ p : ℕ) : ℤ) = 2 ^ p
      rfl
    change 0 < (ofRat p 1).lo + (ofRat p arg).lo
    rw [honeLo]
    exact Nat.add_pos_left (by simp [NatInterval.scale]) _
  have hrecip := contains_reciprocal hsum hbasepos
  have hpow := contains_squareN hrecip k
  have hbound :
      Real.exp (-(x : ℝ)) ≤
        ((1 + (arg : ℝ))⁻¹) ^ (2 ^ k) := by
    simpa [arg] using
      exp_neg_upper_real (x := (x : ℝ)) (by exact_mod_cast hx)
        (2 ^ k) (by positivity)
  change
    (Dyadic.toReal p (0 : ℤ) ≤ Real.exp (-(x : ℝ)) ∧
      Real.exp (-(x : ℝ)) ≤
        Dyadic.toReal p
          (((NatInterval.expNegUpper p x k).hi : ℕ) : ℤ))
  constructor
  · simpa [Dyadic.toReal_zero] using Real.exp_nonneg (-(x : ℝ))
  · exact hbound.trans hpow.2

theorem contains_expPosUpper {x : ℚ} (k : ℕ) (hx : 0 ≤ x)
    (hupper : x < (2 ^ k : ℕ))
    (hbase : 0 < (ofRat p (1 - x / (2 ^ k : ℕ))).lo) :
    Contains (NatInterval.expPosUpper p x k) (Real.exp (x : ℝ)) := by
  let arg : ℚ := x / (2 ^ k : ℕ)
  have harg0 : 0 ≤ arg := div_nonneg hx (by positivity)
  have hdiff : 0 ≤ 1 - arg := by
    dsimp [arg]
    have : (0 : ℚ) < (2 ^ k : ℕ) := by positivity
    rw [sub_nonneg]
    exact (div_le_iff₀ this).mpr (by simpa using hupper.le)
  have harg := contains_ofRat (p := p) (x := 1 - arg) hdiff
  have hrecip := contains_reciprocal harg hbase
  have hpow := contains_squareN hrecip k
  have hbound :
      Real.exp (x : ℝ) ≤
        ((1 - (arg : ℝ))⁻¹) ^ (2 ^ k) := by
    simpa [arg] using
      exp_pos_upper_real (x := (x : ℝ)) (by exact_mod_cast hx)
        (n := 2 ^ k) (by exact_mod_cast hupper)
  change
    (Dyadic.toReal p (0 : ℤ) ≤ Real.exp (x : ℝ) ∧
      Real.exp (x : ℝ) ≤
        Dyadic.toReal p ((NatInterval.expPosUpper p x k).hi : ℤ))
  constructor
  · simpa [Dyadic.toReal_zero] using Real.exp_nonneg (x : ℝ)
  · have hpowUpper :
        ((1 - (arg : ℚ) : ℝ)⁻¹) ^ (2 ^ k) ≤
          Dyadic.toReal p ((NatInterval.expPosUpper p x k).hi : ℤ) := by
      simpa [NatInterval.expPosUpper, NatInterval.upperHull, arg] using hpow.2
    have hbound' : Real.exp (x : ℝ) ≤ ((1 - (arg : ℝ))⁻¹) ^ (2 ^ k) := by
      simpa using hbound
    exact hbound'.trans hpowUpper

end NatInterval
end SparseOneRowCertificate
end CertifiedJL
