/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# A concrete widening smooth cutoff family

The noncompact Peano bridge uses a fixed `C∞` bump whose transition region is
widened by scaling.  This module proves the family facts independently of the
law-specific dominated-convergence argument: compact support, the unit core,
pointwise convergence to one, exact derivative scaling, and bounded base
derivatives.  No cutoff or convergence premise is carried opaquely by a later
theorem.
-/

open Filter Metric
open scoped Topology

namespace CertifiedJL

def upperCutoffRadius (n : ℕ) : ℝ := (n : ℝ) + 1

theorem upperCutoffRadius_pos (n : ℕ) : 0 < upperCutoffRadius n := by
  dsimp [upperCutoffRadius]
  positivity

noncomputable def upperCutoffBase : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

noncomputable def upperCutoff (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨upperCutoffRadius n, 2 * upperCutoffRadius n,
    upperCutoffRadius_pos n,
    by nlinarith [upperCutoffRadius_pos n]⟩

theorem upperCutoff_apply (n : ℕ) (y : ℝ) :
    upperCutoff n y = upperCutoffBase (y / upperCutoffRadius n) := by
  have hRne : upperCutoffRadius n ≠ 0 := (upperCutoffRadius_pos n).ne'
  rw [ContDiffBump.apply, ContDiffBump.apply]
  dsimp [upperCutoff, upperCutoffBase]
  simp only [sub_zero, inv_one, div_one, one_mul]
  change (someContDiffBumpBase ℝ).toFun
      ((2 * upperCutoffRadius n) / upperCutoffRadius n)
      ((upperCutoffRadius n)⁻¹ * y) =
    (someContDiffBumpBase ℝ).toFun 2 (y / upperCutoffRadius n)
  have hscale' : (2 * upperCutoffRadius n) / upperCutoffRadius n = 2 := by
    field_simp
  rw [hscale']
  congr 1
  ring

theorem upperCutoff_contDiff (n : ℕ) :
    ContDiff ℝ 4 (upperCutoff n) := by
  exact (upperCutoff n).contDiff

theorem upperCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (upperCutoff n) := by
  exact (upperCutoff n).hasCompactSupport

theorem upperCutoff_eq_one {n : ℕ} {y : ℝ}
    (hy : |y| ≤ upperCutoffRadius n) : upperCutoff n y = 1 := by
  apply (upperCutoff n).one_of_mem_closedBall
  simpa [upperCutoff, mem_closedBall, Real.norm_eq_abs] using hy

theorem upperCutoff_eq_zero {n : ℕ} {y : ℝ}
    (hy : 2 * upperCutoffRadius n ≤ |y|) : upperCutoff n y = 0 := by
  apply (upperCutoff n).zero_of_le_dist
  simpa [upperCutoff, Real.norm_eq_abs, dist_zero_right] using hy

theorem upperCutoff_nonneg (n : ℕ) (y : ℝ) : 0 ≤ upperCutoff n y := by
  exact (upperCutoff n).nonneg

theorem upperCutoff_le_one (n : ℕ) (y : ℝ) : upperCutoff n y ≤ 1 := by
  exact (upperCutoff n).le_one

theorem upperCutoff_pointwise_tendsto (y : ℝ) :
    Tendsto (fun n : ℕ => upperCutoff n y) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => (upperCutoffRadius n)⁻¹) atTop (𝓝 0) := by
    simpa only [upperCutoffRadius, inv_eq_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have harg : Tendsto (fun n : ℕ => y / upperCutoffRadius n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hbase := upperCutoffBase.continuous.continuousAt.tendsto.comp harg
  have hbase_zero : upperCutoffBase 0 = 1 := by
    apply upperCutoffBase.one_of_mem_closedBall
    change dist (0 : ℝ) 0 ≤ 1
    simp
  rw [hbase_zero] at hbase
  simpa only [Function.comp_def, upperCutoff_apply] using hbase

theorem upperCutoff_iteratedDeriv (n k : ℕ) (y : ℝ) :
    iteratedDeriv k (upperCutoff n) y =
      (upperCutoffRadius n)⁻¹ ^ k *
        iteratedDeriv k (upperCutoffBase) (y / upperCutoffRadius n) := by
  have hfun : (upperCutoff n : ℝ → ℝ) =
      (fun z : ℝ => upperCutoffBase ((upperCutoffRadius n)⁻¹ * z)) := by
    funext z
    rw [upperCutoff_apply]
    simp [div_eq_mul_inv, mul_comm]
  rw [hfun]
  have hbase : ContDiff ℝ k (upperCutoffBase) := upperCutoffBase.contDiff
  have hscale := iteratedDeriv_comp_const_mul (n := k) hbase
    (upperCutoffRadius n)⁻¹
  have hscale_y := congrFun hscale y
  simpa [div_eq_mul_inv, mul_comm] using hscale_y

theorem upperCutoffBase_iteratedDeriv_hasCompactSupport (k : ℕ) :
    HasCompactSupport (iteratedDeriv k (upperCutoffBase)) := by
  induction k with
  | zero =>
      simpa only [iteratedDeriv_zero] using upperCutoffBase.hasCompactSupport
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem upperCutoffBase_iteratedDeriv_bound (k : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, ‖iteratedDeriv k (upperCutoffBase) y‖ ≤ C := by
  have hcont : Continuous (iteratedDeriv k (upperCutoffBase)) :=
    upperCutoffBase.contDiff.continuous_iteratedDeriv' k
  have hbdd : BddAbove (Set.range fun y : ℝ =>
      ‖iteratedDeriv k (upperCutoffBase) y‖) :=
    hcont.norm.bddAbove_range_of_hasCompactSupport
      (upperCutoffBase_iteratedDeriv_hasCompactSupport k).norm
  rcases hbdd with ⟨C, hC⟩
  exact ⟨C, fun y => hC ⟨y, rfl⟩⟩

theorem upperCutoff_iteratedDeriv_bound (k : ℕ) :
    ∃ C : ℝ, ∀ (n : ℕ) (y : ℝ),
      ‖iteratedDeriv k (upperCutoff n) y‖ ≤
        C * (upperCutoffRadius n)⁻¹ ^ k := by
  rcases upperCutoffBase_iteratedDeriv_bound k with ⟨C, hC⟩
  refine ⟨C, fun n y => ?_⟩
  rw [upperCutoff_iteratedDeriv, norm_mul]
  calc
    ‖(upperCutoffRadius n)⁻¹ ^ k‖ *
          ‖iteratedDeriv k (upperCutoffBase)
            (y / upperCutoffRadius n)‖ =
        (upperCutoffRadius n)⁻¹ ^ k *
          ‖iteratedDeriv k (upperCutoffBase)
            (y / upperCutoffRadius n)‖ := by
      rw [Real.norm_eq_abs, abs_pow, abs_inv,
        abs_of_pos (upperCutoffRadius_pos n)]
    _ ≤ (upperCutoffRadius n)⁻¹ ^ k * C := by
      exact mul_le_mul_of_nonneg_left
        (hC (y / upperCutoffRadius n))
        (pow_nonneg (inv_nonneg.mpr (upperCutoffRadius_pos n).le) k)
    _ = C * (upperCutoffRadius n)⁻¹ ^ k := by ring

end CertifiedJL
