/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Spec.ThresholdBudget128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedAnalytic128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Lower
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.RetainedAssembly

/-!
# Large-modulus retained dominant provider at 128 bits

This is the complete `q/A ≥ 3`, residual-ratio-at-least-one-half branch.  It
selects a compact residual subprofile, deletes every other coordinate through
the positive wrapped Fourier series, bounds the retained zero image by the
coupled Holder certificate, and adds the conditioned modular tail exactly
once.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL

private theorem expNegDivOneSubExpNeg_antitone_analytic
    {a₀ a c₀ c : ℝ} (haa : a₀ ≤ a)
    (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) :
    Real.exp (-a) / (1 - Real.exp (-c)) ≤
      Real.exp (-a₀) / (1 - Real.exp (-c₀)) := by
  have hnum : Real.exp (-a) ≤ Real.exp (-a₀) :=
    Real.exp_le_exp.mpr (neg_le_neg haa)
  have hc : 0 < c := hc₀.trans_le hcc
  have hden₀ : 0 < 1 - Real.exp (-c₀) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc₀))
  have hden : 0 < 1 - Real.exp (-c) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hdenOrder : 1 - Real.exp (-c₀) ≤ 1 - Real.exp (-c) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hcc)
    linarith
  exact div_le_div₀ (Real.exp_nonneg _) hnum hden₀ hdenOrder

/-- The two oriented active-image tails decrease as the normalized modulus
increases. -/
theorem retainedActiveImageTail_antitone_modulus_analytic
    {alpha B₀ B : ℝ} (halpha : 0 < alpha)
    (hB₀ : 1 < B₀) (hB : B₀ ≤ B) :
    Real.exp (-alpha * (B - 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
        Real.exp (-alpha * (B + 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B))) ≤
      Real.exp (-alpha * (B₀ - 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B₀ ^ 2 - 2 * B₀))) +
        Real.exp (-alpha * (B₀ + 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B₀ ^ 2 + 2 * B₀))) := by
  have hB1 : 1 < B := hB₀.trans_le hB
  have hminusSq : (B₀ - 1) ^ 2 ≤ (B - 1) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by linarith)).2 (by linarith)
  have hplusSq : (B₀ + 1) ^ 2 ≤ (B + 1) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by linarith)).2 (by linarith)
  have hminusRate :
      3 * B₀ ^ 2 - 2 * B₀ ≤ 3 * B ^ 2 - 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) - 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by linarith
    nlinarith [mul_nonneg hdiff hsum]
  have hplusRate :
      3 * B₀ ^ 2 + 2 * B₀ ≤ 3 * B ^ 2 + 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) + 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by linarith
    nlinarith [mul_nonneg hdiff hsum]
  have hminusRatePos : 0 < 3 * B₀ ^ 2 - 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ - 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hplusRatePos : 0 < 3 * B₀ ^ 2 + 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ + 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hminus := expNegDivOneSubExpNeg_antitone_analytic
    (mul_le_mul_of_nonneg_left hminusSq halpha.le)
    (mul_pos halpha hminusRatePos)
    (mul_le_mul_of_nonneg_left hminusRate halpha.le)
  have hplus := expNegDivOneSubExpNeg_antitone_analytic
    (mul_le_mul_of_nonneg_left hplusSq halpha.le)
    (mul_pos halpha hplusRatePos)
    (mul_le_mul_of_nonneg_left hplusRate halpha.le)
  simpa only [neg_mul] using add_le_add hminus hplus

/-- At public modulus margin three, the exact conditioned image tails are no
larger than the semantic endpoint used by the retained interval certificate. -/
theorem retainedConditionedImageTail_le_semantic_marginThree_analytic
    {q A : ℕ} {V : ℝ} (hA : 0 < A) (hV : 0 ≤ V)
    (hmodulus : 3 ≤ (q : ℝ) / (A : ℝ)) :
    let x : ℝ := 1 + V / (A : ℝ) ^ 2
    (retainedInactiveImageTail q A V (23 / 10) +
        retainedActiveImageTail q A V (23 / 10)) / 2 ≤
      (ThresholdNearCoarse128.semanticInactiveTail x 1 +
        ThresholdNearCoarse128.semanticActiveTail x 1) / 2 := by
  dsimp only
  let u : ℝ := V / (A : ℝ) ^ 2
  let B : ℝ := (q : ℝ) / (A : ℝ)
  let alpha : ℝ := (23 / 10) / (1 + (23 / 10) * u)
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hB : 3 ≤ B := by simpa only [B] using hmodulus
  have hc₀ : 0 < alpha * (3 : ℝ) ^ 2 := by positivity
  have hc : alpha * (3 : ℝ) ^ 2 ≤ alpha * B ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ halpha.le
    exact (sq_le_sq₀ (by norm_num) (by linarith)).2 hB
  have hinactive := twoSidedGeometricTail_antitone hc₀ hc
  have hinactive' :
      2 * Real.exp (-alpha * B ^ 2) /
          (1 - Real.exp (-alpha * B ^ 2) ^ 3) ≤
        2 * Real.exp (-alpha * (3 : ℝ) ^ 2) /
          (1 - Real.exp (-alpha * (3 : ℝ) ^ 2) ^ 3) := by
    simpa only [neg_mul] using hinactive
  have hactive := retainedActiveImageTail_antitone_modulus_analytic
    halpha (by norm_num : (1 : ℝ) < 3) hB
  have hD : ThresholdNearCoarse128.semanticD
      (1 + V / (A : ℝ) ^ 2) 1 = 1 + (23 / 10) * u := by
    dsimp [ThresholdNearCoarse128.semanticD, u]
    ring
  have hT : ThresholdNearCoarse128.semanticT
      (1 + V / (A : ℝ) ^ 2) 1 = alpha := by
    rw [ThresholdNearCoarse128.semanticT, hD]
    dsimp [alpha]
    ring
  have hM : ThresholdNearCoarse128.semanticM 1 = 3 := by
    norm_num [ThresholdNearCoarse128.semanticM]
  have hRho : ThresholdNearCoarse128.semanticRho
      (1 + V / (A : ℝ) ^ 2) 1 =
        Real.exp (-alpha * (3 : ℝ) ^ 2) := by
    rw [ThresholdNearCoarse128.semanticRho, hD]
    congr 1
    dsimp [alpha]
    have hden : 1 + (23 / 10 : ℝ) * u ≠ 0 := by positivity
    field_simp [hden]
    ring
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    retainedInactiveImageTail q A V (23 / 10) +
        retainedActiveImageTail q A V (23 / 10) =
      2 * Real.exp (-alpha * B ^ 2) /
          (1 - Real.exp (-alpha * B ^ 2) ^ 3) +
        (Real.exp (-alpha * (B - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
          Real.exp (-alpha * (B + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) := by
      simp only [retainedInactiveImageTail, retainedActiveImageTail]
      rfl
    _ ≤ 2 * Real.exp (-alpha * (3 : ℝ) ^ 2) /
          (1 - Real.exp (-alpha * (3 : ℝ) ^ 2) ^ 3) +
        (Real.exp (-alpha * ((3 : ℝ) - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * (3 : ℝ) ^ 2 - 2 * 3))) +
          Real.exp (-alpha * ((3 : ℝ) + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * (3 : ℝ) ^ 2 + 2 * 3)))) :=
      add_le_add hinactive' hactive
    _ = ThresholdNearCoarse128.semanticInactiveTail
          (1 + V / (A : ℝ) ^ 2) 1 +
        ThresholdNearCoarse128.semanticActiveTail
          (1 + V / (A : ℝ) ^ 2) 1 := by
      rw [ThresholdNearCoarse128.semanticInactiveTail, hRho]
      simp only [ThresholdNearCoarse128.semanticActiveTail, hT, hM]



/-- The retained large-modulus branch has one-row transform at most `53/100`.
This is the sum of the independently certified `12/25` zero-image cap and
`1/20` conditioned image-tail cap. -/
theorem sparseThresholdDominant_retained_row_le_fiftythree_hundred_of_geometry
    (geometry : CertificateContracts.SparseL2ThresholdDominantRetainedGeometry)
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hq : Odd q) (hi : w i ≠ 0)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmodulus : 3 ≤ (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    ∫ row, Real.exp
        (-((23 / 10 : ℝ) / (dominantAmplitude w i : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      53 / 100 := by
  obtain ⟨support, hlower, hupper⟩ :=
    exists_halfCutoff_dominantRemainder_subprofile w i hi hresidual hmax
  let A := dominantAmplitude w i
  let compact : Fin d → ℤ := fun j =>
    if j ∈ dominantLiftSupport i support then w j else 0
  let V := sqNorm (fun j => if j ∈ support then
    dominantRemainderFinWeights w i j else 0)
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hV : 0 < V := by
    dsimp [V]
    omega
  have hVreal : (0 : ℝ) < V := by exact_mod_cast hV
  have hcompactI : compact i = w i := by simp [compact]
  have hcompactNonzero : compact i ≠ 0 := by simpa [hcompactI] using hi
  have hcompactAmplitude : dominantAmplitude compact i = A := by
    simp [dominantAmplitude, hcompactI, A]
  have hcompactResidual : dominantRemainderFinWeights compact i =
      fun j => if j ∈ support then dominantRemainderFinWeights w i j else 0 :=
    dominantRemainderFinWeights_restrict_liftSupport w i support
  have hcompactNorm : dominantRemainderSqNorm compact i = V := by
    rw [← sqNorm_dominantRemainderFinWeights, hcompactResidual]
  have hxLower : (3 / 2 : ℝ) ≤ 1 + (V : ℝ) / (A : ℝ) ^ 2 := by
    have hlowerR : (A : ℝ) ^ 2 ≤ 2 * (V : ℝ) := by exact_mod_cast hlower
    have hA2 : (0 : ℝ) < (A : ℝ) ^ 2 := sq_pos_of_pos hAreal
    have hhalf : (1 / 2 : ℝ) ≤ (V : ℝ) / (A : ℝ) ^ 2 := by
      apply (le_div_iff₀ hA2).2
      nlinarith
    linarith
  have hxUpper : 1 + (V : ℝ) / (A : ℝ) ^ 2 ≤ 11 / 5 := by
    have hupperR : 5 * (V : ℝ) < 6 * (A : ℝ) ^ 2 := by exact_mod_cast hupper
    have hA2 : (0 : ℝ) < (A : ℝ) ^ 2 := sq_pos_of_pos hAreal
    have hsixfifths : (V : ℝ) / (A : ℝ) ^ 2 ≤ 6 / 5 := by
      apply (div_le_iff₀ hA2).2
      nlinarith
    linarith
  have hcentral := sparseRow_retainedDominantCentral_le_twelve_twentyfive_of_geometry
    geometry w i support hi hlower hupper
  have hcentralCompact :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-((23 / 10 : ℝ) / (dominantAmplitude compact i : ℝ) ^ 2) *
              (((∑ j, row j * compact j : ℤ) : ℝ) ^ 2))
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (12 / 25) := by
    simpa only [hcompactAmplitude] using hcentral
  have hB : 1 < (q : ℝ) / (dominantAmplitude compact i : ℝ) := by
    rw [hcompactAmplitude]
    linarith
  have hassembly := sparseRow_wrapped_le_retainedZero_add_conditionedTail
    compact i (V : ℝ) (23 / 10) (12 / 25)
      hq hcompactNonzero hVreal (by exact_mod_cast hcompactNorm)
      (by norm_num) hB (by norm_num) hcentralCompact
  have htailEndpoint := retainedConditionedImageTail_le_semantic_marginThree_analytic
    (q := q) (A := A) (V := (V : ℝ)) hA hVreal.le hmodulus
  have htailNumeric :=
    geometry.conditionedTail hxLower hxUpper
  have htail :
      (retainedInactiveImageTail q A (V : ℝ) (23 / 10) +
          retainedActiveImageTail q A (V : ℝ) (23 / 10)) / 2 <
        1 / 20 := htailEndpoint.trans_lt htailNumeric
  have hwrappedCap :
      ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q
            ((23 / 10 : ℝ) / (A : ℝ) ^ 2)
            (∑ j, row j * compact j)
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (53 / 100) := by
    have htailENN :
        ENNReal.ofReal
            ((retainedInactiveImageTail q A (V : ℝ) (23 / 10) +
              retainedActiveImageTail q A (V : ℝ) (23 / 10)) / 2) ≤
          ENNReal.ofReal (1 / 20) := ENNReal.ofReal_mono htail.le
    rw [hcompactAmplitude] at hassembly
    have hsum := hassembly.trans (add_le_add_right htailENN _)
    calc
      _ ≤ ENNReal.ofReal (12 / 25) + ENNReal.ofReal (1 / 20) := hsum
      _ = ENNReal.ofReal (53 / 100) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
  have hwrappedReal :
      (∫ row, wrappedGaussianKernel q
          ((23 / 10 : ℝ) / (A : ℝ) ^ 2)
          (∑ j, row j * compact j)
          ∂(sparseRademacherRow d).toMeasure) ≤ 53 / 100 :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 53 / 100)).mp
      hwrappedCap
  have hdelete := sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict
    w (dominantLiftSupport i support) hq
      (by positivity : 0 < (23 / 10 : ℝ) / (A : ℝ) ^ 2)
  exact hdelete.trans (by simpa only [compact] using hwrappedReal)

/-- Compatibility wrapper for the original 128-bit replay contract. -/
theorem sparseThresholdDominant_retained_row_le_fiftythree_hundred_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128)
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hq : Odd q) (hi : w i ≠ 0)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmodulus : 3 ≤ (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    ∫ row, Real.exp
        (-((23 / 10 : ℝ) / (dominantAmplitude w i : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      53 / 100 :=
  sparseThresholdDominant_retained_row_le_fiftythree_hundred_of_geometry
    replay.retainedGeometry w i hq hi hmax hresidual hmodulus

/-- Event-level retained branch.  The high-activity event is contained in the
unconditional lower-tail event, so the retained row cap and its scalar ratio
certificate close this whole parameter region. -/
theorem sparseThresholdDominantHighActivity128_retained_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmodulus : 3 ≤ (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      sparseThreshold128HighActivityBudget := by
  let A := dominantAmplitude w i
  let s : ℝ := (23 / 10) * (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hbReal : (0 : ℝ) < inputThreshold := by exact_mod_cast hinputThreshold
  have hs : 0 < s := by dsimp [s]; positivity
  have hcoefficient : s / (inputThreshold : ℝ) ^ 2 =
      (23 / 10 : ℝ) / (A : ℝ) ^ 2 := by
    dsimp [s]
    field_simp
  have hrow := sparseThresholdDominant_retained_row_le_fiftythree_hundred_of_replay
    replay w i hq hi hmax hresidual hmodulus
  have hrowThreshold :
      ∫ row, Real.exp
          (-(s / (inputThreshold : ℝ) ^ 2) * sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤
        53 / 100 := by
    simpa only [hcoefficient] using hrow
  have hfull := ternaryThresholdLowerTail_from_rowKernelIntegral
    q d w inputThreshold s (53 / 100) hinputThreshold hs hrowThreshold
  have hdomReal :
      (49 : ℝ) * inputThreshold < 50 * A := by
    exact_mod_cast hdominant
  have hsq :
      (2401 : ℝ) * (inputThreshold : ℝ) ^ 2 < 2500 * (A : ℝ) ^ 2 := by
    have hproduct : 0 <
        (50 * (A : ℝ) - 49 * inputThreshold) *
          (50 * (A : ℝ) + 49 * inputThreshold) := by positivity
    nlinarith
  have hthresholdRatio :
      (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2 < 2500 / 2401 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  have hsUpper : s ≤ (23 / 10 : ℝ) * (2500 / 2401) := by
    dsimp [s]
    calc
      (23 / 10 : ℝ) * (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2 =
          (23 / 10) * ((inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2) := by ring
      _ ≤ (23 / 10) * (2500 / 2401) :=
        mul_le_mul_of_nonneg_left hthresholdRatio.le (by norm_num)
  have hratio :
      Real.exp (29 * s) * (53 / 100 : ℝ) ^ 256 <
        (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
    calc
      Real.exp (29 * s) * (53 / 100 : ℝ) ^ 256 ≤
          Real.exp (29 * ((23 / 10 : ℝ) * (2500 / 2401))) *
            (53 / 100 : ℝ) ^ 256 := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hsUpper (by norm_num))
        · positivity
      _ < (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          replay.retainedFinalRatio
  have hfullStrict :
      (eventProbability (sparseRademacherMatrix 256 d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
          inputThreshold q w)).toReal <
        (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 :=
    hfull.trans_lt hratio
  have hjoint :
      eventProbability (sparseRademacherMatrix 256 d)
          (fun J =>
            L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
                inputThreshold q w J ∧
              29 ≤ (dominantActivityCount
                (matrixDominantActivity i J) : ℕ)) ≤
        eventProbability (sparseRademacherMatrix 256 d)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
            inputThreshold q w) := by
    apply eventProbability_mono
    intro J hJ
    exact hJ.1
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by
      unfold sparseThreshold128HighActivityBudget failureTarget
      finiteness)]
  calc
    _ ≤ (eventProbability (sparseRademacherMatrix 256 d)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
            inputThreshold q w)).toReal :=
      ENNReal.toReal_mono
        (by
          unfold eventProbability
          exact PMF.apply_ne_top _ _) hjoint
    _ < (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := hfullStrict
    _ = sparseThreshold128HighActivityBudget.toReal := by
      simp [sparseThreshold128HighActivityBudget, failureTarget]

end CertifiedJL
