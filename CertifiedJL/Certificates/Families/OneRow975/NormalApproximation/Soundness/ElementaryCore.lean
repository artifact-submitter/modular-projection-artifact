import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.ElementaryCore
import CertifiedJL.Probability.NormalApproximation.Tyurin.ElementaryGaussianMoment
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Chunks

open MeasureTheory
namespace CertifiedJL.TyurinModerate
open Probability

theorem coreIntegral_le_closedCoreIntegral {C : Cell} {L : ℝ}
    (hg : geometryCheck C = true) (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hs : C.cutoff * C.rootHi ≤ 5 / 3)
    (hc0 : 0 ≤ (varianceCapInterval C).upperRat)
    (hc1 : (varianceCapInterval C).upperRat < 1) :
    (∫ u : ℝ in 0..(C.cutoff : ℝ), ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤ (closedCoreIntegral C : ℝ) := by
  rcases geometryCheck_sound hg with ⟨hlo, hlohi, _, hcut, hcutU, _⟩
  have hT : (0 : ℝ) < C.cutoff := by exact_mod_cast hcut
  have hb : (0 : ℝ) < C.hi := by exact_mod_cast hlo.trans_le hlohi
  have hLp : 0 < L := (by exact_mod_cast hlo : (0 : ℝ) < C.lo).trans_le hL
  have hTU : (C.cutoff : ℝ) ≤ C.bandwidth := by exact_mod_cast hcutU
  have hs' : (C.cutoff : ℝ) * lyapunovThirdRoot (C.hi : ℝ) ≤ 5 / 3 := by
    calc
      _ ≤ (C.cutoff : ℝ) * (C.rootHi : ℝ) :=
        mul_le_mul_of_nonneg_left (endpoint_root_bounds hg).2 hT.le
      _ ≤ _ := by
        have h := (Rat.cast_le (K := ℝ)).mpr hs
        push_cast at h
        exact h
  let c : ℝ := (varianceCapInterval C).upperRat
  have hcap : lyapunovVarianceCap (C.hi : ℝ) ≤ c :=
    le_upperRat (varianceCapInterval_contains_endpoint hg)
  have hc0' : 0 ≤ c := by dsimp [c]; exact_mod_cast hc0
  have hc1' : c < 1 := by dsimp [c]; exact_mod_cast hc1
  have hactual := tyurinCoreIntegral_le_closed hLp hLb hT (hT.trans_le hTU) hTU
    hs' hcap hc0' hc1'
  have hpi : (piLower : ℝ) ≤ Real.pi := by
    simpa [piLower] using pi_gt_3141592_div_1000000.le
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ (sqrtTwoPiUpper : ℝ) := by
    simpa [sqrtTwoPiUpper] using sqrt_two_pi_lt_250663_div_100000.le
  have hpi0 : (0 : ℝ) < piLower := by norm_num [piLower]
  apply hactual.trans
  unfold closedCoreIntegral
  push_cast
  change _ ≤ (C.hi : ℝ) * (513 / 500) / (2 * (piLower : ℝ)) *
    (sqrtTwoPiUpper : ℝ) / 2 * (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)
  calc
    _ ≤ ((C.hi : ℝ) * (513 / 500) / (2 * (piLower : ℝ))) *
      ((sqrtTwoPiUpper : ℝ) / 2 * (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- The semantic provider from any analytic core bound and unchanged outer
chunks; the core bound need not come from a quadrature certificate. -/
theorem cellCertified_of_coreIntegralBound {C : Cell} {q : ℕ} {outerTotals : List ℚ}
    {coreBound : ℚ}
    (hg : geometryCheck C = true)
    (hcoreBound : ∀ {L : ℝ}, (C.lo : ℝ) ≤ L → L ≤ (C.hi : ℝ) →
      (∫ u : ℝ in 0..(C.cutoff : ℝ), ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤ (coreBound : ℝ))
    (hq : 0 < q) (hcount : C.outerCells = q * outerTotals.length)
    (hchunks : ∀ j (hj : j < outerTotals.length),
      outerExactChunkCheck C (j * q) q outerTotals[j] = true)
    (hfinal : 2 * coreBound +
      2 * (((2 * C.hi * C.bandwidth - 2 * C.hi * C.cutoff) / C.outerCells) *
        outerTotals.sum) + gaussianBudgetUpper C < cellTarget C) : CellCertified C := by
  rcases geometryCheck_sound hg with ⟨hlo, _, _, hcut, hcutU, _⟩
  refine ⟨by exact_mod_cast hcut, by exact_mod_cast hcutU, ?_⟩
  intro L hL hLb
  have hLp : 0 < L := (by exact_mod_cast hlo : (0 : ℝ) < C.lo).trans_le hL
  have hcore := hcoreBound hL hLb
  have houter := outerIntegral_le_of_safe hg hL hLb
    (outerSafe_of_exactChunks hq hcount hchunks)
  have heval := outerIntegralUpper_eq_exactChunks hcount hchunks
  rw [heval] at houter
  have hgauss := gaussianSharpClosedBudget_le hg
  have hfin : 2 * (coreBound : ℝ) +
      2 * ((((2 * C.hi * C.bandwidth - 2 * C.hi * C.cutoff) / C.outerCells) *
        outerTotals.sum : ℚ) : ℝ) + (gaussianBudgetUpper C : ℝ) < (cellTarget C : ℝ) := by
    exact_mod_cast hfinal
  have htarg : (cellTarget C : ℝ) ≤ (3 / 5 : ℝ) * L := by
    unfold cellTarget
    push_cast
    gcongr
  unfold tyurinRationalDStar
  rw [div_lt_iff₀ hLp]
  nlinarith

/-- The existing semantic provider type from a closed pre-switch core bound
and only the unchanged outer chunks. There are no core chunk assumptions. -/
theorem cellCertified_of_closedCore {C : Cell} {q : ℕ} {outerTotals : List ℚ}
    (hg : geometryCheck C = true)
    (hs : C.cutoff * C.rootHi ≤ 5 / 3)
    (hc0 : 0 ≤ (varianceCapInterval C).upperRat)
    (hc1 : (varianceCapInterval C).upperRat < 1)
    (hq : 0 < q) (hcount : C.outerCells = q * outerTotals.length)
    (hchunks : ∀ j (hj : j < outerTotals.length),
      outerExactChunkCheck C (j * q) q outerTotals[j] = true)
    (hfinal : 2 * closedCoreIntegral C +
      2 * (((2 * C.hi * C.bandwidth - 2 * C.hi * C.cutoff) / C.outerCells) *
        outerTotals.sum) + gaussianBudgetUpper C < cellTarget C) : CellCertified C := by
  apply cellCertified_of_coreIntegralBound hg _ hq hcount hchunks hfinal
  intro L hL hLb
  exact coreIntegral_le_closedCoreIntegral hg hL hLb hs hc0 hc1

end CertifiedJL.TyurinModerate
