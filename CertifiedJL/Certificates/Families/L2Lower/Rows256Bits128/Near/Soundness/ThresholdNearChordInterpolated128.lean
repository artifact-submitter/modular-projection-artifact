/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Semiconvex128

/-! # Semiconvex interpolation between the five certified endpoints -/

namespace CertifiedJL
namespace ThresholdNearChord128

open Set

private theorem semanticEnvelope_lt_681_div_1250_of_adjacent_endpoints
    (replay : CertificateContracts.SparseL2ThresholdNearReplay128)
    {x a l u y : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500)
    (hlBand : (4 / 5 : ℝ) ≤ l) (huBand : u ≤ 1)
    (hlu : l < u) (hy : y ∈ Icc l u)
    (hwidth : u - l = 1 / 20)
    (hl : semanticEnvelope x a l < (endpointCap128 : ℚ))
    (hu : semanticEnvelope x a u < (endpointCap128 : ℚ)) :
    semanticEnvelope x a y < 681 / 1250 := by
  have hxa : 0 < x - a := by nlinarith [hx.1, ha.2]
  have hlpos : 0 < l := by linarith
  have hcentral := le_max_endpoints_add_semiconvex_defect
    (f := fun z ↦ semanticChordCentral x a z)
    (f' := fun z ↦ semanticChordCentralPrime x a z)
    (f'' := fun z ↦ semanticChordCentralSecond x a z)
    (M := 81 / 20) hlu hy (by norm_num)
    (by
      intro z hz
      exact (hasDerivAt_semanticChordCentral hxa
        (hlpos.trans_le hz.1)).continuousAt.continuousWithinAt)
    (by
      intro z hz
      exact hasDerivAt_semanticChordCentral hxa (hlpos.trans hz.1))
    (by
      intro z hz
      exact hasDerivAt_semanticChordCentralPrime hxa (hlpos.trans hz.1))
    (by
      intro z hz
      exact (replay.curvature
        hx ha ⟨hlBand.trans hz.1.le, hz.2.le.trans huBand⟩).le)
  let tail : ℝ :=
    (ThresholdNearCoarse128.semanticInactiveTail x a +
      ThresholdNearCoarse128.semanticActiveTail x a) / 2
  have hl' : semanticChordCentral x a l + tail < (endpointCap128 : ℚ) := by
    simpa only [semanticEnvelope, tail] using hl
  have hu' : semanticChordCentral x a u + tail < (endpointCap128 : ℚ) := by
    simpa only [semanticEnvelope, tail] using hu
  have hmax : max (semanticChordCentral x a l) (semanticChordCentral x a u) +
      tail < (endpointCap128 : ℚ) := by
    rcases le_total (semanticChordCentral x a l)
        (semanticChordCentral x a u) with hle | hle
    · rw [max_eq_right hle]
      exact hu'
    · rw [max_eq_left hle]
      exact hl'
  change semanticChordCentral x a y + tail < 681 / 1250
  calc
    semanticChordCentral x a y + tail ≤
        (max (semanticChordCentral x a l) (semanticChordCentral x a u) + tail) +
          (81 / 20) * (u - l) ^ 2 / 8 := by linarith
    _ < (endpointCap128 : ℚ) + (81 / 20 : ℝ) * (u - l) ^ 2 / 8 := by
      gcongr
    _ = 681 / 1250 := by norm_num [endpointCap128, hwidth]

/-- Uniform high-Holder endpoint interpolation on the entire normalized near
band. -/
theorem semanticEnvelope_lt_681_div_1250_interpolated_of_replay
    (replay : CertificateContracts.SparseL2ThresholdNearReplay128)
    {x a y : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500)
    (hy : (4 / 5 : ℝ) ≤ y ∧ y ≤ 1) :
    semanticEnvelope x a y < 681 / 1250 := by
  have h4 := replay.endpointFourFifths hx ha
  have h17 := replay.endpointSeventeenTwentieths hx ha
  have h9 := replay.endpointNineTenths hx ha
  have h19 := replay.endpointNineteenTwentieths hx ha
  have h1 := replay.endpointOne hx ha
  by_cases h17y : y ≤ 17 / 20
  · exact semanticEnvelope_lt_681_div_1250_of_adjacent_endpoints replay
      hx ha (by norm_num) (by norm_num) (by norm_num)
      ⟨hy.1, h17y⟩ (by norm_num) h4 h17
  by_cases h9y : y ≤ 9 / 10
  · exact semanticEnvelope_lt_681_div_1250_of_adjacent_endpoints replay
      hx ha (by norm_num) (by norm_num) (by norm_num)
      ⟨le_of_not_ge h17y, h9y⟩ (by norm_num) h17 h9
  by_cases h19y : y ≤ 19 / 20
  · exact semanticEnvelope_lt_681_div_1250_of_adjacent_endpoints replay
      hx ha (by norm_num) (by norm_num) (by norm_num)
      ⟨le_of_not_ge h9y, h19y⟩ (by norm_num) h9 h19
  · exact semanticEnvelope_lt_681_div_1250_of_adjacent_endpoints replay
      hx ha (by norm_num) (by norm_num) (by norm_num)
      ⟨le_of_not_ge h19y, hy.2⟩ (by norm_num) h19 h1

end ThresholdNearChord128
end CertifiedJL
