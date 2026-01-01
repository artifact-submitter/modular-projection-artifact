import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.CrossingCore
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.ElementaryCore
import CertifiedJL.Probability.NormalApproximation.Tyurin.CrossingCore

open MeasureTheory
namespace CertifiedJL.TyurinModerate
open Probability

theorem coreIntegral_le_crossingCoreIntegral {C : Cell} {L : ℝ}
    (hg : geometryCheck C = true) (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hc0 : 0 ≤ crossingCoreCap C) (hc1 : crossingCoreCap C < 1) :
    (∫ u : ℝ in 0..(C.cutoff : ℝ), ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤ (crossingCoreIntegral C : ℝ) := by
  rcases geometryCheck_sound hg with ⟨hlo, hlohi, _, hcut, hcutU, _⟩
  have hT : (0 : ℝ) < C.cutoff := by exact_mod_cast hcut
  have hb : (0 : ℝ) < C.hi := by exact_mod_cast hlo.trans_le hlohi
  have hLp : 0 < L := (by exact_mod_cast hlo : (0 : ℝ) < C.lo).trans_le hL
  have hTU : (C.cutoff : ℝ) ≤ C.bandwidth := by exact_mod_cast hcutU
  let c : ℝ := crossingCoreCap C
  have hcap : lyapunovVarianceCap (C.hi : ℝ) ≤ c := by
    apply (le_upperRat (varianceCapInterval_contains_endpoint hg)).trans
    have h : (varianceCapInterval C).upperRat ≤ crossingCoreCap C := le_max_left _ _
    dsimp [c]
    exact_mod_cast h
  have hcutCap : 2 * (C.hi : ℝ) * (C.cutoff : ℝ) / 5 +
      25 / (27 * (C.cutoff : ℝ) ^ 2) ≤ c := by
    have hq : 2 * C.hi * C.cutoff / 5 + 25 / (27 * C.cutoff ^ 2) ≤ crossingCoreCap C :=
      le_max_right _ _
    have h := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at h
    exact h
  have hc0' : 0 ≤ c := by dsimp [c]; exact_mod_cast hc0
  have hc1' : c < 1 := by dsimp [c]; exact_mod_cast hc1
  have hactual := tyurinCoreIntegral_le_crossingClosed hLp hLb hT (hT.trans_le hTU) hTU
    hcap hcutCap hc0' hc1'
  have hpi : (piLower : ℝ) ≤ Real.pi := by
    simpa [piLower] using pi_gt_3141592_div_1000000.le
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ (sqrtTwoPiUpper : ℝ) := by
    simpa [sqrtTwoPiUpper] using sqrt_two_pi_lt_250663_div_100000.le
  have hpi0 : (0 : ℝ) < piLower := by norm_num [piLower]
  apply hactual.trans
  unfold crossingCoreIntegral
  push_cast
  change _ ≤ (C.hi : ℝ) * (513 / 500) / (2 * (piLower : ℝ)) *
    (sqrtTwoPiUpper : ℝ) / 2 * (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)
  calc
    _ ≤ ((C.hi : ℝ) * (513 / 500) / (2 * (piLower : ℝ))) *
      ((sqrtTwoPiUpper : ℝ) / 2 * (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- The original semantic cell certificate, including crossing cells, from
a closed core bound and only the unchanged outer exact chunks. -/
theorem cellCertified_of_crossingCore {C : Cell} {q : ℕ} {outerTotals : List ℚ}
    (hg : geometryCheck C = true) (hc0 : 0 ≤ crossingCoreCap C)
    (hc1 : crossingCoreCap C < 1)
    (hq : 0 < q) (hcount : C.outerCells = q * outerTotals.length)
    (hchunks : ∀ j (hj : j < outerTotals.length),
      outerExactChunkCheck C (j * q) q outerTotals[j] = true)
    (hfinal : 2 * crossingCoreIntegral C +
      2 * (((2 * C.hi * C.bandwidth - 2 * C.hi * C.cutoff) / C.outerCells) *
        outerTotals.sum) + gaussianBudgetUpper C < cellTarget C) : CellCertified C := by
  apply cellCertified_of_coreIntegralBound hg _ hq hcount hchunks hfinal
  intro L hL hLb
  exact coreIntegral_le_crossingCoreIntegral hg hL hLb hc0 hc1

end CertifiedJL.TyurinModerate
