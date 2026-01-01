import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.HermiteMajorant

/-!
# Paper parameters for the sparse lower-tail Hermite bound

This file pins the five rational interpolation nodes and transfers the
semantic majorization theorem through `u = cos² θ` and `α = p / 2`.
-/

noncomputable section

namespace CertifiedJL

/-- The five rational Hermite nodes used by the sparse lower-tail argument. -/
def sparseHermiteNodes : Fin 5 → ℝ :=
  ![21 / 250, 303 / 1000, 581 / 1000, 417 / 500, 1961 / 2000]

theorem sparseHermiteNodes_strictMono : StrictMono sparseHermiteNodes := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp [sparseHermiteNodes] <;> norm_num

theorem sparseHermiteNodes_zero_pos : 0 < sparseHermiteNodes 0 := by
  norm_num [sparseHermiteNodes]

theorem sparseHermiteNodes_four_lt_one : sparseHermiteNodes 4 < 1 := by
  simp [sparseHermiteNodes]
  norm_num

/-- Squaring and halving the exponent gives the absolute-value power.  The
zero case is split explicitly, so this theorem applies when the cosine
vanishes. -/
theorem sq_rpow_half_eq_abs_rpow {x p : ℝ} (hp : 0 < p) :
    (x ^ 2).rpow (p / 2) = |x|.rpow p := by
  by_cases hx : x = 0
  · subst x
    rw [zero_pow (by norm_num), Real.rpow_eq_pow, Real.zero_rpow (by linarith),
      abs_zero, Real.rpow_eq_pow, Real.zero_rpow hp.ne']
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
  rw [show x ^ 2 = |x| ^ 2 by exact (sq_abs x).symm]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

/-- The paper-node Hermite polynomial bounds the cosine power for `2 < p < 4`.
The statement is valid at a zero cosine and at `cos² θ = 1`. -/
theorem abs_cos_rpow_le_sparseHermite {p θ : ℝ} (hp₂ : 2 < p) (hp₄ : p < 4) :
    |Real.cos θ|.rpow p ≤
      (chosenHermiteInterpolant (p / 2) sparseHermiteNodes).eval ((Real.cos θ) ^ 2) := by
  rw [← sq_rpow_half_eq_abs_rpow (by linarith)]
  apply chosenHermiteInterpolant_majorizes
  · linarith
  · linarith
  · exact sparseHermiteNodes_strictMono
  · exact sparseHermiteNodes_zero_pos
  · exact sparseHermiteNodes_four_lt_one
  · constructor
    · positivity
    · nlinarith [Real.cos_mem_Icc θ |>.1, Real.cos_mem_Icc θ |>.2]

/-- Direct endpoint consumer for a vanishing cosine. -/
theorem abs_cos_rpow_le_sparseHermite_of_cos_eq_zero {p θ : ℝ}
    (hp₂ : 2 < p) (_hp₄ : p < 4) (hcos : Real.cos θ = 0) :
    |Real.cos θ|.rpow p ≤
      (chosenHermiteInterpolant (p / 2) sparseHermiteNodes).eval ((Real.cos θ) ^ 2) := by
  rw [hcos, abs_zero, zero_pow (by norm_num),
    chosenHermiteInterpolant_eval_zero (p / 2) sparseHermiteNodes
      sparseHermiteNodes_strictMono sparseHermiteNodes_zero_pos,
    Real.rpow_eq_pow, Real.zero_rpow]
  linarith

end CertifiedJL
