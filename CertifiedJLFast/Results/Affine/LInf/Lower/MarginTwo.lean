/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.Transport.Scaling
import CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints
import CertifiedJLFast.Results.Affine.LInf.Lower.Direct

/-! # Affine upper endpoints and margin-two lower endpoints -/

namespace CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo

open CertifiedJL

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower192Cap93Over500Margin2Bits129 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 192,
        coordinateCap := { numerator := 93, denominator := 500, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 129) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower192Cap279Over1000Bits129.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower256Cap4Over25Margin2Bits197 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 4, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 197) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower256Cap331Over1500Margin2Bits133 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 331, denominator := 1500, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 133) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower256Cap331Over1000Bits133.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower384Cap331Over1500Margin2Bits200 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 384,
        coordinateCap := { numerator := 331, denominator := 1500, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 200) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower384Cap331Over1000Bits200.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower512Cap331Over1500Margin2Bits266 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 512,
        coordinateCap := { numerator := 331, denominator := 1500, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 266) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower512Cap331Over1000Bits266.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower512Cap92Over375Margin2Bits206 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 512,
        coordinateCap := { numerator := 92, denominator := 375, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 206) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower512Cap46Over125Bits206.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower256Cap67Over300Margin2Bits130 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 67, denominator := 300, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 130) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower256Cap6Over25Margin2Bits109 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 6, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 109) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower256Cap9Over25Bits109.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

/-- Exact odd-scale transport of the margin-three endpoint; the failure budget is unchanged. -/
theorem ternaryAffineLInfThresholdLower462Cap6Over25Margin2Bits197 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 462,
        coordinateCap := { numerator := 6, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 197) := by
  have h := CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower462Cap9Over25Bits197.twoThirds
  intro q d w b shift hq hc hb hn hm
  have hmargin : InputThresholdWithinModulus
      (NonnegativeRatio.ofNat 3).twoThirds q b := by
    dsimp [InputThresholdWithinModulus, NonnegativeRatio.twoThirds,
      NonnegativeRatio.ofNat] at hm ⊢
    omega
  apply (eventProbability_mono _ ?_).trans_lt (h q d w b shift hq hc hb hn hmargin)
  intro J hJ j
  have hj := hJ j
  norm_num [AffineLInfThresholdSmallProjection, NonnegativeRatio.twoThirds] at hj ⊢
  omega

end CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo
