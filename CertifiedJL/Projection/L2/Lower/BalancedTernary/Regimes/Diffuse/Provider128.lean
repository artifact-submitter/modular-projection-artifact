/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Soundness.ThresholdBits128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedProfiles
import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.High
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Low

/-! # Complete diffuse provider for the 128-bit public-threshold assembly -/

namespace CertifiedJL

/-- Retain a diffuse profile with the shift-stable wrapped `97/200` bound. -/
theorem sparseThresholdDiffuseWrappedRowBound_marginThree_of_replay
    (scalarReplay : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (tailReplay : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    (highReplay : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128) :
    SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200) := by
  intro q d w inputThreshold hq hpositive hnorm hmarginNat hdiffuse
  obtain ⟨support, hlower, hupper⟩ :=
    exists_threshold_subprofile_of_three_quarters
      w inputThreshold hpositive hnorm hdiffuse
  let v : Fin d → ℤ := fun i ↦ if i ∈ support then w i else 0
  let B : ℝ := inputThreshold
  let V : ℝ := sqNorm v
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast hpositive
  have hVlower : B ^ 2 ≤ V := by
    dsimp [B, V]
    exact_mod_cast hlower
  have hV : 0 < V := lt_of_lt_of_le (sq_pos_of_pos hB) hVlower
  have hVupper : V ≤ (25 / 16 : ℝ) * B ^ 2 := by
    have hupper' : 16 * V < 25 * B ^ 2 := by
      dsimp [B, V]
      exact_mod_cast hupper
    nlinarith
  have h_norm : ∑ i, (v i : ℝ) ^ 2 = V := by
    exact (realCast_sqNorm v).symm
  have hmargin : 3 * B ≤ (q : ℝ) := by
    dsimp [B]
    exact_mod_cast hmarginNat
  have hdiffuseReal : ∀ i, 16 * (v i : ℝ) ^ 2 ≤ 9 * B ^ 2 := by
    intro i
    by_cases hi : i ∈ support
    · have hsquare := Nat.pow_le_pow_left (hdiffuse i) 2
      have hnat : 16 * (w i).natAbs ^ 2 ≤ 9 * inputThreshold ^ 2 := by
        simpa [mul_pow] using hsquare
      have hnatReal :
          (16 : ℝ) * ((w i).natAbs : ℝ) ^ 2 ≤
            9 * (inputThreshold : ℝ) ^ 2 := by
        exact_mod_cast hnat
      dsimp [v, B]
      simp only [if_pos hi]
      have habs : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [habs, sq_abs] at hnatReal
      exact hnatReal
    · simp [v, hi, sq_nonneg B]
  have hcompact :
      ∫ row, wrappedGaussianKernel q ((33 / 10 : ℝ) / B ^ 2)
          (∑ i, row i * v i)
          ∂(sparseRademacherRow d).toMeasure ≤
        97 / 200 := by
    by_cases hlow : V ≤ (11 / 10 : ℝ) * B ^ 2
    · exact ThresholdDiffuseLow.sparseRow_diffuse_lowMass_wrapped_le_97_div_200
        scalarReplay tailReplay v q B V hq hB hV h_norm hmargin hdiffuseReal hVlower hlow
    · have hhigh : (11 / 10 : ℝ) * B ^ 2 ≤ V := le_of_not_ge hlow
      exact sparseRow_diffuse_highMass_wrapped_le_97_div_200
        highReplay v q B V hq hB hV h_norm hmargin hdiffuseReal hhigh hVupper
  exact ⟨support, hcompact⟩

/-- The original centered row provider is a corollary of the wrapped interface. -/
theorem sparseThresholdDiffuseRow128Bound_marginThree_of_replay
    (scalarReplay : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (tailReplay : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    (highReplay : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128) :
    SparseThresholdDiffuseRow128BoundAt (NonnegativeRatio.ofNat 3) := by
  intro q d w b hq _hcentered hpositive hnorm hmodulus hdiffuse
  have hmargin : 3 * b ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmodulus
  obtain ⟨support, hwrapped⟩ :=
    sparseThresholdDiffuseWrappedRowBound_marginThree_of_replay
      scalarReplay tailReplay highReplay q d w b hq hpositive hnorm hmargin hdiffuse
  exact (sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict w support hq
    (by positivity : 0 < (33 / 10 : ℝ) / (b : ℝ) ^ 2)).trans hwrapped

end CertifiedJL
