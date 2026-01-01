/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.GammaInteger

/-!
# Exact Gamma certificates for the higher-security upper obstructions

The four semantic certificate propositions in this file are the exact
integer-shape Gamma inequalities used by the finite flat-vector witnesses.
Their providers use only interval-reflected exponential enclosures and exact
rational arithmetic.
-/

namespace CertifiedJL
namespace Probability

/-- Gamma boundary for `(rows,bits,threshold) = (256,192,404)`. -/
def GammaRows256Threshold404Bits192Certificate : Prop :=
  gammaSurvivalNat 128 404 >
    (1089 / 1000 : ℝ) * (2 : ℝ)⁻¹ ^ 192

/-- A strict rational upper enclosure for `exp (404/128)`. -/
theorem exp_101_32_lt :
    Real.exp (101 / 32 : ℝ) < 234824 / 10000 := by
  have hcontains :=
    Exp.posUpper_contains
      (p := 64) (k := 24) (x := (101 / 32 : ℚ))
      (by norm_num) (by norm_num) (by
        change 0 < Dyadic.roundDown 64 (1 - (101 / 32) / 2 ^ 24)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [Dyadic.scale])
  simpa using
    (Interval.lt_of_contains_of_upperLTCheck
      (bound := (234824 / 10000 : ℚ)) hcontains (by
        set_option maxRecDepth 100000 in
          decide +kernel))

/-- Exact cross-multiplication for the shape-128 boundary. -/
theorem gamma128_404_rational_comparison :
    (234824 / 10000 : ℝ) ^ 128 <
      (1000 * 2 ^ 192 / 1089 : ℝ) *
        ∑ r ∈ Finset.Icc 120 127, (404 : ℝ) ^ r / r.factorial := by
  set_option maxRecDepth 2000000 in
    norm_num [Finset.sum_Icc_succ_top]

/-- Kernel-checked provider for the 256-row, 192-bit Gamma boundary. -/
theorem gammaRows256Threshold404Bits192_verified :
    GammaRows256Threshold404Bits192Certificate := by
  have hexpPower :
      Real.exp (404 : ℝ) < (234824 / 10000 : ℝ) ^ 128 := by
    calc
      Real.exp (404 : ℝ) = Real.exp (101 / 32 : ℝ) ^ 128 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ < (234824 / 10000 : ℝ) ^ 128 :=
        pow_lt_pow_left₀ exp_101_32_lt (Real.exp_nonneg _) (by norm_num)
  have htail :
      (∑ r ∈ Finset.Icc 120 127, (404 : ℝ) ^ r / r.factorial) ≤
        ∑ r ∈ Finset.range 128, (404 : ℝ) ^ r / r.factorial := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      exact Finset.mem_range.mpr (by omega)
    · intro r _ _
      positivity
  have hexpTail :
      Real.exp (404 : ℝ) <
        (1000 * 2 ^ 192 / 1089 : ℝ) *
          ∑ r ∈ Finset.range 128, (404 : ℝ) ^ r / r.factorial :=
    hexpPower.trans <| gamma128_404_rational_comparison.trans_le <|
      mul_le_mul_of_nonneg_left htail (by positivity)
  unfold GammaRows256Threshold404Bits192Certificate gammaSurvivalNat
  rw [Real.exp_neg]
  have hexpPos : 0 < Real.exp (404 : ℝ) := Real.exp_pos _
  rw [gt_iff_lt, inv_mul_eq_div, lt_div_iff₀ hexpPos]
  calc
    (1089 / 1000 : ℝ) * (2 : ℝ)⁻¹ ^ 192 * Real.exp 404 =
        (1089 / (1000 * 2 ^ 192) : ℝ) * Real.exp 404 := by
      norm_num [inv_pow]
    _ < (1089 / (1000 * 2 ^ 192) : ℝ) *
        ((1000 * 2 ^ 192 / 1089 : ℝ) *
          ∑ r ∈ Finset.range 128,
            (404 : ℝ) ^ r / r.factorial) :=
      mul_lt_mul_of_pos_left hexpTail (by positivity)
    _ = ∑ r ∈ Finset.range 128,
          (404 : ℝ) ^ r / r.factorial := by
      field_simp

/-- Gamma boundary for `(rows,bits,threshold) = (384,192,507)`. -/
def GammaRows384Threshold507Bits192Certificate : Prop :=
  gammaSurvivalNat 192 507 >
    (8 / 5 : ℝ) * (2 : ℝ)⁻¹ ^ 192

theorem exp_169_64_highSecurity_lt :
    Real.exp (169 / 64 : ℝ) < 1402197 / 100000 := by
  have hcontains :=
    Exp.posUpper_contains
      (p := 64) (k := 24) (x := (169 / 64 : ℚ))
      (by norm_num) (by norm_num) (by
        change 0 < Dyadic.roundDown 64 (1 - (169 / 64) / 2 ^ 24)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [Dyadic.scale])
  simpa using
    (Interval.lt_of_contains_of_upperLTCheck
      (bound := (1402197 / 100000 : ℚ)) hcontains (by
        set_option maxRecDepth 100000 in
          decide +kernel))

theorem gamma192_507_rational_comparison :
    (1402197 / 100000 : ℝ) ^ 192 <
      (5 * 2 ^ 192 / 8 : ℝ) *
        ∑ r ∈ Finset.Icc 184 191, (507 : ℝ) ^ r / r.factorial := by
  set_option maxRecDepth 2000000 in
    norm_num [Finset.sum_Icc_succ_top]

/-- Kernel-checked provider for the 384-row, 192-bit Gamma boundary. -/
theorem gammaRows384Threshold507Bits192_verified :
    GammaRows384Threshold507Bits192Certificate := by
  have hexpPower :
      Real.exp (507 : ℝ) < (1402197 / 100000 : ℝ) ^ 192 := by
    calc
      Real.exp (507 : ℝ) = Real.exp (169 / 64 : ℝ) ^ 192 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ < (1402197 / 100000 : ℝ) ^ 192 :=
        pow_lt_pow_left₀ exp_169_64_highSecurity_lt
          (Real.exp_nonneg _) (by norm_num)
  have htail :
      (∑ r ∈ Finset.Icc 184 191, (507 : ℝ) ^ r / r.factorial) ≤
        ∑ r ∈ Finset.range 192, (507 : ℝ) ^ r / r.factorial := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      exact Finset.mem_range.mpr (by omega)
    · intro r _ _
      positivity
  have hexpTail :
      Real.exp (507 : ℝ) <
        (5 * 2 ^ 192 / 8 : ℝ) *
          ∑ r ∈ Finset.range 192, (507 : ℝ) ^ r / r.factorial :=
    hexpPower.trans <| gamma192_507_rational_comparison.trans_le <|
      mul_le_mul_of_nonneg_left htail (by positivity)
  unfold GammaRows384Threshold507Bits192Certificate gammaSurvivalNat
  rw [Real.exp_neg]
  have hexpPos : 0 < Real.exp (507 : ℝ) := Real.exp_pos _
  rw [gt_iff_lt, inv_mul_eq_div, lt_div_iff₀ hexpPos]
  calc
    (8 / 5 : ℝ) * (2 : ℝ)⁻¹ ^ 192 * Real.exp 507 =
        (8 / (5 * 2 ^ 192) : ℝ) * Real.exp 507 := by
      norm_num [inv_pow]
    _ < (8 / (5 * 2 ^ 192) : ℝ) *
        ((5 * 2 ^ 192 / 8 : ℝ) *
          ∑ r ∈ Finset.range 192,
            (507 : ℝ) ^ r / r.factorial) :=
      mul_lt_mul_of_pos_left hexpTail (by positivity)
    _ = ∑ r ∈ Finset.range 192,
          (507 : ℝ) ^ r / r.factorial := by
      field_simp

/-- Gamma boundary for `(rows,bits,threshold) = (512,192,605)`. -/
def GammaRows512Threshold605Bits192Certificate : Prop :=
  gammaSurvivalNat 256 605 >
    (321 / 250 : ℝ) * (2 : ℝ)⁻¹ ^ 192

theorem exp_605_256_lt :
    Real.exp (605 / 256 : ℝ) < 1062577 / 100000 := by
  have hcontains :=
    Exp.posUpper_contains
      (p := 64) (k := 24) (x := (605 / 256 : ℚ))
      (by norm_num) (by norm_num) (by
        change 0 < Dyadic.roundDown 64 (1 - (605 / 256) / 2 ^ 24)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [Dyadic.scale])
  simpa using
    (Interval.lt_of_contains_of_upperLTCheck
      (bound := (1062577 / 100000 : ℚ)) hcontains (by
        set_option maxRecDepth 100000 in
          decide +kernel))

theorem gamma256_605_rational_comparison :
    (1062577 / 100000 : ℝ) ^ 256 <
      (250 * 2 ^ 192 / 321 : ℝ) *
        ∑ r ∈ Finset.Icc 246 255, (605 : ℝ) ^ r / r.factorial := by
  set_option maxRecDepth 2000000 in
    norm_num [Finset.sum_Icc_succ_top]

/-- Kernel-checked provider for the shared 512-row, 192-bit Gamma boundary. -/
theorem gammaRows512Threshold605Bits192_verified :
    GammaRows512Threshold605Bits192Certificate := by
  have hexpPower :
      Real.exp (605 : ℝ) < (1062577 / 100000 : ℝ) ^ 256 := by
    calc
      Real.exp (605 : ℝ) = Real.exp (605 / 256 : ℝ) ^ 256 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ < (1062577 / 100000 : ℝ) ^ 256 :=
        pow_lt_pow_left₀ exp_605_256_lt (Real.exp_nonneg _) (by norm_num)
  have htail :
      (∑ r ∈ Finset.Icc 246 255, (605 : ℝ) ^ r / r.factorial) ≤
        ∑ r ∈ Finset.range 256, (605 : ℝ) ^ r / r.factorial := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      exact Finset.mem_range.mpr (by omega)
    · intro r _ _
      positivity
  have hexpTail :
      Real.exp (605 : ℝ) <
        (250 * 2 ^ 192 / 321 : ℝ) *
          ∑ r ∈ Finset.range 256, (605 : ℝ) ^ r / r.factorial :=
    hexpPower.trans <| gamma256_605_rational_comparison.trans_le <|
      mul_le_mul_of_nonneg_left htail (by positivity)
  unfold GammaRows512Threshold605Bits192Certificate gammaSurvivalNat
  rw [Real.exp_neg]
  have hexpPos : 0 < Real.exp (605 : ℝ) := Real.exp_pos _
  rw [gt_iff_lt, inv_mul_eq_div, lt_div_iff₀ hexpPos]
  calc
    (321 / 250 : ℝ) * (2 : ℝ)⁻¹ ^ 192 * Real.exp 605 =
        (321 / (250 * 2 ^ 192) : ℝ) * Real.exp 605 := by
      norm_num [inv_pow]
    _ < (321 / (250 * 2 ^ 192) : ℝ) *
        ((250 * 2 ^ 192 / 321 : ℝ) *
          ∑ r ∈ Finset.range 256,
            (605 : ℝ) ^ r / r.factorial) :=
      mul_lt_mul_of_pos_left hexpTail (by positivity)
    _ = ∑ r ∈ Finset.range 256,
          (605 : ℝ) ^ r / r.factorial := by
      field_simp

/-- Gamma boundary for `(rows,bits,threshold) = (512,256,678)`. -/
def GammaRows512Threshold678Bits256Certificate : Prop :=
  gammaSurvivalNat 256 678 >
    (179 / 100 : ℝ) * (2 : ℝ)⁻¹ ^ 256

theorem exp_339_128_lt :
    Real.exp (339 / 128 : ℝ) < 1413195 / 100000 := by
  have hcontains :=
    Exp.posUpper_contains
      (p := 64) (k := 24) (x := (339 / 128 : ℚ))
      (by norm_num) (by norm_num) (by
        change 0 < Dyadic.roundDown 64 (1 - (339 / 128) / 2 ^ 24)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [Dyadic.scale])
  simpa using
    (Interval.lt_of_contains_of_upperLTCheck
      (bound := (1413195 / 100000 : ℚ)) hcontains (by
        set_option maxRecDepth 100000 in
          decide +kernel))

theorem gamma256_678_rational_comparison :
    (1413195 / 100000 : ℝ) ^ 256 <
      (100 * 2 ^ 256 / 179 : ℝ) *
        ∑ r ∈ Finset.Icc 248 255, (678 : ℝ) ^ r / r.factorial := by
  set_option maxRecDepth 2000000 in
    norm_num [Finset.sum_Icc_succ_top]

/-- Kernel-checked provider for the shared 512-row, 256-bit Gamma boundary. -/
theorem gammaRows512Threshold678Bits256_verified :
    GammaRows512Threshold678Bits256Certificate := by
  have hexpPower :
      Real.exp (678 : ℝ) < (1413195 / 100000 : ℝ) ^ 256 := by
    calc
      Real.exp (678 : ℝ) = Real.exp (339 / 128 : ℝ) ^ 256 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ < (1413195 / 100000 : ℝ) ^ 256 :=
        pow_lt_pow_left₀ exp_339_128_lt (Real.exp_nonneg _) (by norm_num)
  have htail :
      (∑ r ∈ Finset.Icc 248 255, (678 : ℝ) ^ r / r.factorial) ≤
        ∑ r ∈ Finset.range 256, (678 : ℝ) ^ r / r.factorial := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      exact Finset.mem_range.mpr (by omega)
    · intro r _ _
      positivity
  have hexpTail :
      Real.exp (678 : ℝ) <
        (100 * 2 ^ 256 / 179 : ℝ) *
          ∑ r ∈ Finset.range 256, (678 : ℝ) ^ r / r.factorial :=
    hexpPower.trans <| gamma256_678_rational_comparison.trans_le <|
      mul_le_mul_of_nonneg_left htail (by positivity)
  unfold GammaRows512Threshold678Bits256Certificate gammaSurvivalNat
  rw [Real.exp_neg]
  have hexpPos : 0 < Real.exp (678 : ℝ) := Real.exp_pos _
  rw [gt_iff_lt, inv_mul_eq_div, lt_div_iff₀ hexpPos]
  calc
    (179 / 100 : ℝ) * (2 : ℝ)⁻¹ ^ 256 * Real.exp 678 =
        (179 / (100 * 2 ^ 256) : ℝ) * Real.exp 678 := by
      norm_num [inv_pow]
    _ < (179 / (100 * 2 ^ 256) : ℝ) *
        ((100 * 2 ^ 256 / 179 : ℝ) *
          ∑ r ∈ Finset.range 256,
            (678 : ℝ) ^ r / r.factorial) :=
      mul_lt_mul_of_pos_left hexpTail (by positivity)
    _ = ∑ r ∈ Finset.range 256,
          (678 : ℝ) ^ r / r.factorial := by
      field_simp

end Probability
end CertifiedJL
