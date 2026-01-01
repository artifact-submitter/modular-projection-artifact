/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.Endpoints.ThresholdNearChordEndpointOne_15_128

/-! # Verified fixed endpoints for near-band interpolation -/

namespace CertifiedJL.ThresholdNearChord128

private theorem endpoint_fourFifths_check :
    endpointPlanCheck128 (endpointCell128 (4 / 5))
      ((endpointReplayAt128 endpointPaths_4_div_5).plan (endpointCell128 (4 / 5))) = true := by
  have hunits :
      (endpointReplayAt128 endpointPaths_4_div_5).units (endpointCell128 (4 / 5)) = [
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 0,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 1,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 2,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 3,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 4,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 5,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 6,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 7,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 8,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 9,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 10,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 11,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 12,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 13,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 14,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 15,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 16,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 17,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 18,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 19,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 20,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 21,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 22,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 23,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 24,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 25,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 26,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 27,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 28,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 29,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 30,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 31,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 32,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 33,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 34,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 35,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 36,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 37,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 38,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 39,
        endpointUnitFromPaths128 (4 / 5) endpointPaths_4_div_5 40 ] := by
    rfl
  have hall :
      ((endpointReplayAt128 endpointPaths_4_div_5).units (endpointCell128 (4 / 5))).all
        endpointUnitPass128 = true := by
    rw [hunits]
    change (List.range 41).all
      (endpointUnitPassFromPaths128 (4 / 5) endpointPaths_4_div_5) = true
    norm_num
    intro index hindex
    interval_cases index <;> norm_num [
      endpoint4Unit00_check,
      endpoint4Unit01_check,
      endpoint4Unit02_check,
      endpoint4Unit03_check,
      endpoint4Unit04_check,
      endpoint4Unit05_check,
      endpoint4Unit06_check,
      endpoint4Unit07_check,
      endpoint4Unit08_check,
      endpoint4Unit09_check,
      endpoint4Unit10_check,
      endpoint4Unit11_check,
      endpoint4Unit12_check,
      endpoint4Unit13_check,
      endpoint4Unit14_check,
      endpoint4Unit15_check,
      endpoint4Unit16_check,
      endpoint4Unit17_check,
      endpoint4Unit18_check,
      endpoint4Unit19_check,
      endpoint4Unit20_check,
      endpoint4Unit21_check,
      endpoint4Unit22_check,
      endpoint4Unit23_check,
      endpoint4Unit24_check,
      endpoint4Unit25_check,
      endpoint4Unit26_check,
      endpoint4Unit27_check,
      endpoint4Unit28_check,
      endpoint4Unit29_check,
      endpoint4Unit30_check,
      endpoint4Unit31_check,
      endpoint4Unit32_check,
      endpoint4Unit33_check,
      endpoint4Unit34_check,
      endpoint4Unit35_check,
      endpoint4Unit36_check,
      endpoint4Unit37_check,
      endpoint4Unit38_check,
      endpoint4Unit39_check,
      endpoint4Unit40_check]
  rw [← EndpointReplay.check_eq_planCheck, EndpointReplay.check_eq_units_all]
  exact hall

theorem semanticEnvelope_lt_endpointCap128_at_fourFifths
    {x a : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500) :
    semanticEnvelope x a (4 / 5) < (endpointCap128 : ℚ) := by
  apply semanticEnvelope_lt_endpointCap128_of_planCheck
    (endpointCell128 (4 / 5))
    ((endpointReplayAt128 endpointPaths_4_div_5).plan (endpointCell128 (4 / 5)))
  · simpa [endpointCell128] using
      And.intro hx.1 (And.intro hx.2 (And.intro ha.1
        (And.intro ha.2 (And.intro (le_refl (4 / 5 : ℝ))
          (le_refl (4 / 5 : ℝ))))))
  · exact endpoint_fourFifths_check

private theorem endpoint_seventeenTwentieths_check :
    endpointPlanCheck128 (endpointCell128 (17 / 20))
      ((endpointReplayAt128 endpointPaths_17_div_20).plan (endpointCell128 (17 / 20))) = true := by
  have hunits :
      (endpointReplayAt128 endpointPaths_17_div_20).units (endpointCell128 (17 / 20)) = [
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 0,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 1,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 2,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 3,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 4,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 5,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 6,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 7,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 8,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 9,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 10,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 11,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 12,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 13,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 14,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 15,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 16,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 17,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 18,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 19,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 20,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 21,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 22,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 23,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 24,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 25,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 26,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 27,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 28,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 29,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 30,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 31,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 32,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 33,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 34,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 35,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 36,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 37,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 38,
        endpointUnitFromPaths128 (17 / 20) endpointPaths_17_div_20 39 ] := by
    rfl
  have hall :
      ((endpointReplayAt128 endpointPaths_17_div_20).units (endpointCell128 (17 / 20))).all
        endpointUnitPass128 = true := by
    rw [hunits]
    change (List.range 40).all
      (endpointUnitPassFromPaths128 (17 / 20) endpointPaths_17_div_20) = true
    norm_num
    intro index hindex
    interval_cases index <;> norm_num [
      endpoint17Unit00_check,
      endpoint17Unit01_check,
      endpoint17Unit02_check,
      endpoint17Unit03_check,
      endpoint17Unit04_check,
      endpoint17Unit05_check,
      endpoint17Unit06_check,
      endpoint17Unit07_check,
      endpoint17Unit08_check,
      endpoint17Unit09_check,
      endpoint17Unit10_check,
      endpoint17Unit11_check,
      endpoint17Unit12_check,
      endpoint17Unit13_check,
      endpoint17Unit14_check,
      endpoint17Unit15_check,
      endpoint17Unit16_check,
      endpoint17Unit17_check,
      endpoint17Unit18_check,
      endpoint17Unit19_check,
      endpoint17Unit20_check,
      endpoint17Unit21_check,
      endpoint17Unit22_check,
      endpoint17Unit23_check,
      endpoint17Unit24_check,
      endpoint17Unit25_check,
      endpoint17Unit26_check,
      endpoint17Unit27_check,
      endpoint17Unit28_check,
      endpoint17Unit29_check,
      endpoint17Unit30_check,
      endpoint17Unit31_check,
      endpoint17Unit32_check,
      endpoint17Unit33_check,
      endpoint17Unit34_check,
      endpoint17Unit35_check,
      endpoint17Unit36_check,
      endpoint17Unit37_check,
      endpoint17Unit38_check,
      endpoint17Unit39_check]
  rw [← EndpointReplay.check_eq_planCheck, EndpointReplay.check_eq_units_all]
  exact hall

theorem semanticEnvelope_lt_endpointCap128_at_seventeenTwentieths
    {x a : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500) :
    semanticEnvelope x a (17 / 20) < (endpointCap128 : ℚ) := by
  apply semanticEnvelope_lt_endpointCap128_of_planCheck
    (endpointCell128 (17 / 20))
    ((endpointReplayAt128 endpointPaths_17_div_20).plan (endpointCell128 (17 / 20)))
  · simpa [endpointCell128] using
      And.intro hx.1 (And.intro hx.2 (And.intro ha.1
        (And.intro ha.2 (And.intro (le_refl (17 / 20 : ℝ))
          (le_refl (17 / 20 : ℝ))))))
  · exact endpoint_seventeenTwentieths_check

private theorem endpoint_nineTenths_check :
    endpointPlanCheck128 (endpointCell128 (9 / 10))
      ((endpointReplayAt128 endpointPaths_9_div_10).plan (endpointCell128 (9 / 10))) = true := by
  have hunits :
      (endpointReplayAt128 endpointPaths_9_div_10).units (endpointCell128 (9 / 10)) = [
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 0,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 1,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 2,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 3,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 4,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 5,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 6,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 7,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 8,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 9,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 10,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 11,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 12,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 13,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 14,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 15,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 16,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 17,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 18,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 19,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 20,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 21,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 22,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 23,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 24,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 25,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 26,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 27,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 28,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 29,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 30,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 31,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 32,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 33,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 34,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 35,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 36,
        endpointUnitFromPaths128 (9 / 10) endpointPaths_9_div_10 37 ] := by
    rfl
  have hall :
      ((endpointReplayAt128 endpointPaths_9_div_10).units (endpointCell128 (9 / 10))).all
        endpointUnitPass128 = true := by
    rw [hunits]
    change (List.range 38).all
      (endpointUnitPassFromPaths128 (9 / 10) endpointPaths_9_div_10) = true
    norm_num
    intro index hindex
    interval_cases index <;> norm_num [
      endpoint9Unit00_check,
      endpoint9Unit01_check,
      endpoint9Unit02_check,
      endpoint9Unit03_check,
      endpoint9Unit04_check,
      endpoint9Unit05_check,
      endpoint9Unit06_check,
      endpoint9Unit07_check,
      endpoint9Unit08_check,
      endpoint9Unit09_check,
      endpoint9Unit10_check,
      endpoint9Unit11_check,
      endpoint9Unit12_check,
      endpoint9Unit13_check,
      endpoint9Unit14_check,
      endpoint9Unit15_check,
      endpoint9Unit16_check,
      endpoint9Unit17_check,
      endpoint9Unit18_check,
      endpoint9Unit19_check,
      endpoint9Unit20_check,
      endpoint9Unit21_check,
      endpoint9Unit22_check,
      endpoint9Unit23_check,
      endpoint9Unit24_check,
      endpoint9Unit25_check,
      endpoint9Unit26_check,
      endpoint9Unit27_check,
      endpoint9Unit28_check,
      endpoint9Unit29_check,
      endpoint9Unit30_check,
      endpoint9Unit31_check,
      endpoint9Unit32_check,
      endpoint9Unit33_check,
      endpoint9Unit34_check,
      endpoint9Unit35_check,
      endpoint9Unit36_check,
      endpoint9Unit37_check]
  rw [← EndpointReplay.check_eq_planCheck, EndpointReplay.check_eq_units_all]
  exact hall

theorem semanticEnvelope_lt_endpointCap128_at_nineTenths
    {x a : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500) :
    semanticEnvelope x a (9 / 10) < (endpointCap128 : ℚ) := by
  apply semanticEnvelope_lt_endpointCap128_of_planCheck
    (endpointCell128 (9 / 10))
    ((endpointReplayAt128 endpointPaths_9_div_10).plan (endpointCell128 (9 / 10)))
  · simpa [endpointCell128] using
      And.intro hx.1 (And.intro hx.2 (And.intro ha.1
        (And.intro ha.2 (And.intro (le_refl (9 / 10 : ℝ))
          (le_refl (9 / 10 : ℝ))))))
  · exact endpoint_nineTenths_check

private theorem endpoint_nineteenTwentieths_check :
    endpointPlanCheck128 (endpointCell128 (19 / 20))
      ((endpointReplayAt128 endpointPaths_19_div_20).plan (endpointCell128 (19 / 20))) = true := by
  have hunits :
      (endpointReplayAt128 endpointPaths_19_div_20).units (endpointCell128 (19 / 20)) = [
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 0,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 1,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 2,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 3,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 4,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 5,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 6,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 7,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 8,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 9,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 10,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 11,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 12,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 13,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 14,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 15,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 16,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 17,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 18,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 19,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 20,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 21,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 22,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 23,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 24,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 25,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 26,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 27,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 28,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 29,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 30,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 31,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 32,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 33,
        endpointUnitFromPaths128 (19 / 20) endpointPaths_19_div_20 34 ] := by
    rfl
  have hall :
      ((endpointReplayAt128 endpointPaths_19_div_20).units (endpointCell128 (19 / 20))).all
        endpointUnitPass128 = true := by
    rw [hunits]
    change (List.range 35).all
      (endpointUnitPassFromPaths128 (19 / 20) endpointPaths_19_div_20) = true
    norm_num
    intro index hindex
    interval_cases index <;> norm_num [
      endpoint19Unit00_check,
      endpoint19Unit01_check,
      endpoint19Unit02_check,
      endpoint19Unit03_check,
      endpoint19Unit04_check,
      endpoint19Unit05_check,
      endpoint19Unit06_check,
      endpoint19Unit07_check,
      endpoint19Unit08_check,
      endpoint19Unit09_check,
      endpoint19Unit10_check,
      endpoint19Unit11_check,
      endpoint19Unit12_check,
      endpoint19Unit13_check,
      endpoint19Unit14_check,
      endpoint19Unit15_check,
      endpoint19Unit16_check,
      endpoint19Unit17_check,
      endpoint19Unit18_check,
      endpoint19Unit19_check,
      endpoint19Unit20_check,
      endpoint19Unit21_check,
      endpoint19Unit22_check,
      endpoint19Unit23_check,
      endpoint19Unit24_check,
      endpoint19Unit25_check,
      endpoint19Unit26_check,
      endpoint19Unit27_check,
      endpoint19Unit28_check,
      endpoint19Unit29_check,
      endpoint19Unit30_check,
      endpoint19Unit31_check,
      endpoint19Unit32_check,
      endpoint19Unit33_check,
      endpoint19Unit34_check]
  rw [← EndpointReplay.check_eq_planCheck, EndpointReplay.check_eq_units_all]
  exact hall

theorem semanticEnvelope_lt_endpointCap128_at_nineteenTwentieths
    {x a : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500) :
    semanticEnvelope x a (19 / 20) < (endpointCap128 : ℚ) := by
  apply semanticEnvelope_lt_endpointCap128_of_planCheck
    (endpointCell128 (19 / 20))
    ((endpointReplayAt128 endpointPaths_19_div_20).plan (endpointCell128 (19 / 20)))
  · simpa [endpointCell128] using
      And.intro hx.1 (And.intro hx.2 (And.intro ha.1
        (And.intro ha.2 (And.intro (le_refl (19 / 20 : ℝ))
          (le_refl (19 / 20 : ℝ))))))
  · exact endpoint_nineteenTwentieths_check

private theorem endpoint_one_check :
    endpointPlanCheck128 (endpointCell128 (1))
      ((endpointReplayAt128 endpointPaths_one).plan (endpointCell128 (1))) = true := by
  have hunits :
      (endpointReplayAt128 endpointPaths_one).units (endpointCell128 (1)) = [
        endpointUnitFromPaths128 (1) endpointPaths_one 0,
        endpointUnitFromPaths128 (1) endpointPaths_one 1,
        endpointUnitFromPaths128 (1) endpointPaths_one 2,
        endpointUnitFromPaths128 (1) endpointPaths_one 3,
        endpointUnitFromPaths128 (1) endpointPaths_one 4,
        endpointUnitFromPaths128 (1) endpointPaths_one 5,
        endpointUnitFromPaths128 (1) endpointPaths_one 6,
        endpointUnitFromPaths128 (1) endpointPaths_one 7,
        endpointUnitFromPaths128 (1) endpointPaths_one 8,
        endpointUnitFromPaths128 (1) endpointPaths_one 9,
        endpointUnitFromPaths128 (1) endpointPaths_one 10,
        endpointUnitFromPaths128 (1) endpointPaths_one 11,
        endpointUnitFromPaths128 (1) endpointPaths_one 12,
        endpointUnitFromPaths128 (1) endpointPaths_one 13,
        endpointUnitFromPaths128 (1) endpointPaths_one 14,
        endpointUnitFromPaths128 (1) endpointPaths_one 15,
        endpointUnitFromPaths128 (1) endpointPaths_one 16,
        endpointUnitFromPaths128 (1) endpointPaths_one 17,
        endpointUnitFromPaths128 (1) endpointPaths_one 18,
        endpointUnitFromPaths128 (1) endpointPaths_one 19,
        endpointUnitFromPaths128 (1) endpointPaths_one 20,
        endpointUnitFromPaths128 (1) endpointPaths_one 21,
        endpointUnitFromPaths128 (1) endpointPaths_one 22,
        endpointUnitFromPaths128 (1) endpointPaths_one 23,
        endpointUnitFromPaths128 (1) endpointPaths_one 24,
        endpointUnitFromPaths128 (1) endpointPaths_one 25,
        endpointUnitFromPaths128 (1) endpointPaths_one 26,
        endpointUnitFromPaths128 (1) endpointPaths_one 27,
        endpointUnitFromPaths128 (1) endpointPaths_one 28,
        endpointUnitFromPaths128 (1) endpointPaths_one 29,
        endpointUnitFromPaths128 (1) endpointPaths_one 30 ] := by
    rfl
  have hall :
      ((endpointReplayAt128 endpointPaths_one).units (endpointCell128 (1))).all
        endpointUnitPass128 = true := by
    rw [hunits]
    change (List.range 31).all
      (endpointUnitPassFromPaths128 (1) endpointPaths_one) = true
    norm_num
    intro index hindex
    interval_cases index <;> norm_num [
      endpointOneUnit00_check,
      endpointOneUnit01_check,
      endpointOneUnit02_check,
      endpointOneUnit03_check,
      endpointOneUnit04_check,
      endpointOneUnit05_check,
      endpointOneUnit06_check,
      endpointOneUnit07_check,
      endpointOneUnit08_check,
      endpointOneUnit09_check,
      endpointOneUnit10_check,
      endpointOneUnit11_check,
      endpointOneUnit12_check,
      endpointOneUnit13_check,
      endpointOneUnit14_check,
      endpointOneUnit15_check,
      endpointOneUnit16_check,
      endpointOneUnit17_check,
      endpointOneUnit18_check,
      endpointOneUnit19_check,
      endpointOneUnit20_check,
      endpointOneUnit21_check,
      endpointOneUnit22_check,
      endpointOneUnit23_check,
      endpointOneUnit24_check,
      endpointOneUnit25_check,
      endpointOneUnit26_check,
      endpointOneUnit27_check,
      endpointOneUnit28_check,
      endpointOneUnit29_check,
      endpointOneUnit30_check]
  rw [← EndpointReplay.check_eq_planCheck, EndpointReplay.check_eq_units_all]
  exact hall

theorem semanticEnvelope_lt_endpointCap128_at_one
    {x a : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500) :
    semanticEnvelope x a (1) < (endpointCap128 : ℚ) := by
  apply semanticEnvelope_lt_endpointCap128_of_planCheck
    (endpointCell128 (1))
    ((endpointReplayAt128 endpointPaths_one).plan (endpointCell128 (1)))
  · simpa [endpointCell128] using
      And.intro hx.1 (And.intro hx.2 (And.intro ha.1
        (And.intro ha.2 (And.intro (le_refl (1 : ℝ))
          (le_refl (1 : ℝ))))))
  · exact endpoint_one_check

end CertifiedJL.ThresholdNearChord128
