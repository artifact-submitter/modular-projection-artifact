/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.DeltaMonotonicity
import CertifiedJL.Probability.NormalApproximation.Tyurin.ProductCertificate

/-!
# Sharp endpoint envelopes on a Lyapunov cell

The `49/50` product envelope has a tiny downward jump at `2Lu=4`, so it is
not globally monotone in `L`.  On a narrow rational cell `[a,b]`, however,
the sharp rational endpoint envelope at `b` also dominates the cubic switch
limit.  Thus the checker retains `49/50`; no global weakening is needed.
-/

open Set

namespace CertifiedJL
namespace Probability

/-- Sharp, trigonometric-free endpoint envelope used by one Lyapunov cell. -/
noncomputable def tyurinCellProductEnvelope (b u : ℝ) : ℝ :=
  if 2 * b * u < 4 then
    Real.exp (-(u ^ 2) / 2 + b * u ^ 3 / 5)
  else
    Real.exp
      (-(tyurinCosineLoss / (4 * b ^ 2) *
        tyurinRationalCosineLower (2 * b * u)))

private theorem rationalCosine_switch
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 471 / 100) :
    tyurinCosineLoss *
        tyurinRationalCosineLower x ≤ x ^ 2 / 10 := by
  have hbranch : x ≤ 471 / 100 := hx1
  rw [tyurinRationalCosineLower, if_pos hbranch]
  unfold tyurinCosineLoss
  have hid :
      x ^ 2 / 10 -
          (49 / 50 : ℝ) *
            (2 - (x - 157 / 50) ^ 2 / 2) =
        601 / 250000 +
          (x - 4) * (59 * x / 100 - 1793 / 2500) := by
    ring
  rw [← sub_nonneg, hid]
  exact add_nonneg (by norm_num)
    (mul_nonneg (sub_nonneg.mpr hx0) (by nlinarith))

private theorem cubicEnvelope_le_switch
    {L u : ℝ} (_hu : 0 ≤ u) (hfreq : 2 * L * u ≤ 4) :
    Real.exp (-(u ^ 2) / 2 + L * u ^ 3 / 5) ≤
      Real.exp (-(u ^ 2) / 10) := by
  apply Real.exp_le_exp.mpr
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hmul : L * u ^ 3 ≤ 2 * u ^ 2 := by
    calc
      L * u ^ 3 = (L * u) * u ^ 2 := by ring
      _ ≤ 2 * u ^ 2 := by
        gcongr
        nlinarith
  nlinarith

private theorem switch_le_rationalEndpoint
    {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u)
    (hleft : 4 ≤ 2 * b * u)
    (hright : 2 * b * u ≤ 471 / 100) :
    Real.exp (-(u ^ 2) / 10) ≤
      Real.exp
        (-(tyurinCosineLoss / (4 * b ^ 2) *
          tyurinRationalCosineLower (2 * b * u))) := by
  apply Real.exp_le_exp.mpr
  have hpoly :=
    rationalCosine_switch hleft hright
  have huPos : 0 < u := by
    by_contra h
    have : u = 0 := le_antisymm (le_of_not_gt h) hu
    subst u
    norm_num at hleft
  have hbu : 2 * b * u ≠ 0 := by positivity
  have hrearrange :
      tyurinCosineLoss *
            tyurinRationalCosineLower (2 * b * u) /
          (4 * b ^ 2) ≤
        u ^ 2 / 10 := by
    have hden : 0 < 4 * b ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    calc
      tyurinCosineLoss *
            tyurinRationalCosineLower (2 * b * u)
          ≤ (2 * b * u) ^ 2 / 10 := hpoly
      _ = u ^ 2 / 10 * (4 * b ^ 2) := by ring
  have hneg := neg_le_neg hrearrange
  calc
    -u ^ 2 / 10 = -(u ^ 2 / 10) := by ring
    _ ≤ -(tyurinCosineLoss *
          tyurinRationalCosineLower (2 * b * u) /
          (4 * b ^ 2)) := hneg
    _ = -(tyurinCosineLoss / (4 * b ^ 2) *
          tyurinRationalCosineLower (2 * b * u)) := by ring

/--
Uniform sharp product envelope on a narrow Lyapunov cell.  The ratio
`b/a ≤ 471/400` is exactly what keeps a switch-crossing frequency inside the
left rational cosine polynomial.
-/
theorem tyurinProductEnvelope_le_cellEndpoint
    {a L b u : ℝ} (ha : 0 < a) (haL : a ≤ L) (hLb : L ≤ b)
    (hu : 0 ≤ u) (hratio : b / a ≤ 471 / 400)
    (hband : 2 * b * u ≤ 157 / 25) :
    tyurinProductEnvelope L u ≤
      tyurinCellProductEnvelope b u := by
  have hL : 0 < L := ha.trans_le haL
  have hb : 0 < b := hL.trans_le hLb
  have hfreq :
      2 * L * u ≤ 2 * b * u := by
    nlinarith
  have hbandPi : 2 * b * u ≤ 2 * Real.pi := by
    nlinarith [pi_gt_157_div_50]
  unfold tyurinCellProductEnvelope
  by_cases hbFirst : 2 * b * u < 4
  · rw [if_pos hbFirst]
    have hLFirst : 2 * L * |u| < 4 := by
      rw [abs_of_nonneg hu]
      exact hfreq.trans_lt hbFirst
    unfold tyurinProductEnvelope tyurinB
      tyurinRationalM tyurinRationalA
    rw [abs_of_nonneg hu,
      if_pos (by simpa [abs_of_nonneg hu] using hLFirst)]
    apply Real.exp_le_exp.mpr
    have hu3 : 0 ≤ u ^ 3 := by positivity
    nlinarith
  · rw [if_neg hbFirst]
    have hbFour : 4 ≤ 2 * b * u := le_of_not_gt hbFirst
    by_cases hLFirst : 2 * L * u < 4
    · have hactual :
          tyurinProductEnvelope L u =
            Real.exp (-(u ^ 2) / 2 + L * u ^ 3 / 5) := by
        unfold tyurinProductEnvelope tyurinB
          tyurinRationalM tyurinRationalA
        rw [abs_of_nonneg hu, if_pos hLFirst]
        congr 1
        ring
      rw [hactual]
      apply (cubicEnvelope_le_switch hu hLFirst.le).trans
      apply switch_le_rationalEndpoint hb hu hbFour
      have haInv : 0 < a := ha
      have hbu :
          2 * b * u = (b / a) * (2 * a * u) := by
        field_simp [ha.ne']
      rw [hbu]
      have haFreq : 2 * a * u < 4 := by
        have : 2 * a * u ≤ 2 * L * u := by nlinarith
        exact this.trans_lt hLFirst
      have hratio0 : 0 ≤ b / a := by positivity
      calc
        b / a * (2 * a * u) ≤ b / a * 4 := by gcongr
        _ ≤ (471 / 400 : ℝ) * 4 := by gcongr
        _ = 471 / 100 := by norm_num
    · have hLFour : 4 ≤ 2 * L * u := le_of_not_gt hLFirst
      have hLband : 2 * L * u ≤ 2 * Real.pi :=
        hfreq.trans hbandPi
      have hxLmem : 2 * L * u ∈ Icc 4 (2 * Real.pi) :=
        ⟨hLFour, hLband⟩
      have hxBmem : 2 * b * u ∈ Icc 4 (2 * Real.pi) :=
        ⟨hbFour, hbandPi⟩
      have hprofile :=
        antitoneOn_tyurinCosineProfile hxLmem hxBmem hfreq
      have hprofileScale :
          -tyurinCosineLoss * u ^ 2 *
                tyurinCosineProfile (2 * L * u) ≤
            -tyurinCosineLoss * u ^ 2 *
                tyurinCosineProfile (2 * b * u) := by
        have hfront : -tyurinCosineLoss * u ^ 2 ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (by
              unfold tyurinCosineLoss
              norm_num)) (sq_nonneg u)
        exact mul_le_mul_of_nonpos_left hprofile hfront
      have hleftRewrite :
          -2 * tyurinCosineLoss / (2 * L) ^ 2 *
                (1 - Real.cos (2 * L * u)) / 2 =
            -tyurinCosineLoss * u ^ 2 *
              tyurinCosineProfile (2 * L * u) := by
        have huPos : 0 < u := by
          by_contra h
          have : u = 0 := le_antisymm (le_of_not_gt h) hu
          subst u
          norm_num at hLFour
        change
          -2 * tyurinCosineLoss / (2 * L) ^ 2 *
                (1 - Real.cos (2 * L * u)) / 2 =
            -tyurinCosineLoss * u ^ 2 *
              ((1 - Real.cos (2 * L * u)) /
                (2 * L * u) ^ 2)
        field_simp [hL.ne', huPos.ne']
      have hrightRewrite :
          -tyurinCosineLoss * u ^ 2 *
                tyurinCosineProfile (2 * b * u) =
            -(tyurinCosineLoss / (4 * b ^ 2) *
              (1 - Real.cos (2 * b * u))) := by
        have huPos : 0 < u := by
          by_contra h
          have : u = 0 := le_antisymm (le_of_not_gt h) hu
          subst u
          norm_num at hbFour
        change
          -tyurinCosineLoss * u ^ 2 *
                ((1 - Real.cos (2 * b * u)) /
                  (2 * b * u) ^ 2) =
            -(tyurinCosineLoss / (4 * b ^ 2) *
              (1 - Real.cos (2 * b * u)))
        field_simp [hb.ne', huPos.ne']
        norm_num
        ring
      have hlower :=
        tyurinRationalCosineLower_le_one_sub_cos hbFour hband
      have hfactor :
          0 ≤ tyurinCosineLoss / (4 * b ^ 2) := by
        unfold tyurinCosineLoss
        positivity
      have hrational :
          -(tyurinCosineLoss / (4 * b ^ 2) *
              (1 - Real.cos (2 * b * u))) ≤
            -(tyurinCosineLoss / (4 * b ^ 2) *
              tyurinRationalCosineLower (2 * b * u)) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlower hfactor)
      unfold tyurinProductEnvelope tyurinB tyurinRationalM
      rw [abs_of_nonneg hu]
      have hnotFirst : ¬ 2 * L * u < 4 := not_lt.mpr hLFour
      rw [if_neg hnotFirst, if_pos hLband]
      apply Real.exp_le_exp.mpr
      rw [hleftRewrite]
      exact hprofileScale.trans (hrightRewrite ▸ hrational)

end Probability
end CertifiedJL
