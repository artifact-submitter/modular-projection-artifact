/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author

Portions of the endpoint-continuity argument are adapted from
`MathExtras/NumberTheory/Analysis/VaalerJhatCornerOne.lean` in
`gersh/ternary-goldbach-lean`, commit
`89416190c037331d7ebc04cd62ddb974cfb4dfcf` (Apache-2.0),
copyright (c) 2026 Gershon Bialer.
-/

import CertifiedJL.Analysis.Fourier.Beurling.Frequency

/-!
# Continuity of Vaaler's compact frequency multiplier

This file proves global continuity of `beurlingJHat`.  The only delicate
points are the support endpoints `±1`.  Near `1`, the apparently singular
factor is rewritten as

`|t| cos(π|t|) / sinc(π(1-|t|))`,

whose denominator tends to one.  The endpoint value is therefore zero.
The argument at `-1` follows by evenness.
-/

open Filter Set Topology

namespace CertifiedJL
namespace Probability

theorem continuousAt_beurlingJHat_of_abs_lt_one
    {t : ℝ} (ht : |t| < 1) :
    ContinuousAt beurlingJHat t := by
  have habs : ContinuousAt (fun s : ℝ => |s|) t :=
    continuous_abs.continuousAt
  have hcot :=
    continuousAt_regularizedFrequencyCot_of_abs_lt_one ht
  have hinner : ContinuousAt
      (fun s : ℝ =>
        Real.pi * (1 - |s|) * regularizedFrequencyCot s + |s|) t :=
    (((continuousAt_const.mul
      (continuousAt_const.sub habs)).mul hcot).add habs)
  refine hinner.congr_of_eventuallyEq ?_
  have hopen : IsOpen {s : ℝ | |s| < 1} :=
    isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds ht] with s hs
  simp [beurlingJHat, hs]

theorem continuousAt_beurlingJHat_of_one_lt_abs
    {t : ℝ} (ht : 1 < |t|) :
    ContinuousAt beurlingJHat t := by
  have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t :=
    continuousAt_const
  refine hzero.congr_of_eventuallyEq ?_
  have hopen : IsOpen {s : ℝ | 1 < |s|} :=
    isOpen_lt continuous_const continuous_abs
  filter_upwards [hopen.mem_nhds ht] with s hs
  simp [beurlingJHat, not_lt.mpr hs.le]

/-- Continuous reference expression for `beurlingJHat` near `1`. -/
private noncomputable def beurlingJHatEndpointRef (s : ℝ) : ℝ :=
  |s| * Real.cos (Real.pi * |s|) /
      Real.sinc (Real.pi * (1 - |s|)) + |s|

private theorem beurlingJHatEndpointRef_one :
    beurlingJHatEndpointRef 1 = 0 := by
  norm_num [beurlingJHatEndpointRef, Real.sinc_zero, Real.cos_pi]

private theorem continuousAt_beurlingJHatEndpointRef_one :
    ContinuousAt beurlingJHatEndpointRef 1 := by
  have habs : ContinuousAt (fun s : ℝ => |s|) 1 :=
    continuous_abs.continuousAt
  have hsincArg :
      ContinuousAt (fun s : ℝ => Real.pi * (1 - |s|)) 1 :=
    continuousAt_const.mul (continuousAt_const.sub habs)
  have hsinc :
      ContinuousAt
        (fun s : ℝ => Real.sinc (Real.pi * (1 - |s|))) 1 :=
    Real.continuous_sinc.continuousAt.comp hsincArg
  have hsincNe :
      Real.sinc (Real.pi * (1 - |(1 : ℝ)|)) ≠ 0 := by
    norm_num [Real.sinc_zero]
  have hcos :
      ContinuousAt (fun s : ℝ => Real.cos (Real.pi * |s|)) 1 := by
    fun_prop
  exact ((habs.mul hcos).div hsinc hsincNe).add habs

private theorem beurlingJHat_eq_endpointRef
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    beurlingJHat s = beurlingJHatEndpointRef s := by
  have hsabs : |s| = s := abs_of_pos hs0
  have h1s : 0 < 1 - s := by linarith
  have hsinEq :
      Real.sin (Real.pi * s) =
        Real.sin (Real.pi * (1 - s)) := by
    have harg :
        Real.pi * (1 - s) = Real.pi - Real.pi * s := by ring
    rw [harg, Real.sin_pi_sub]
  have hpi1s :
      Real.pi * (1 - s) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero h1s.ne'
  have hsNe : s ≠ 0 := hs0.ne'
  rw [beurlingJHat_of_abs_lt_one (by simpa [hsabs] using hs1),
    regularizedFrequencyCot_eq_mul_cot
      (by simpa [hsabs] using hs1) hsNe,
    Real.cot_eq_cos_div_sin, hsinEq]
  unfold beurlingJHatEndpointRef
  rw [hsabs, Real.sinc_of_ne_zero hpi1s]
  field_simp

theorem continuousAt_beurlingJHat_one :
    ContinuousAt beurlingJHat 1 := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · have href :
        ContinuousWithinAt beurlingJHatEndpointRef (Iic 1) 1 :=
      continuousAt_beurlingJHatEndpointRef_one.continuousWithinAt
    refine href.congr_of_eventuallyEq_of_mem ?_ (by simp)
    have hset :
        Iic 1 ∩ Ioo (1 / 2 : ℝ) 2 ∈ 𝓝[Iic 1] (1 : ℝ) :=
      inter_mem_nhdsWithin (Iic 1)
        (Ioo_mem_nhds (by norm_num) (by norm_num))
    refine eventuallyEq_of_mem hset ?_
    intro s hs
    obtain ⟨hsle, hslo, _⟩ := hs
    have hs_le' : s ≤ 1 := Set.mem_Iic.mp hsle
    rcases eq_or_lt_of_le hs_le' with rfl | hslt
    · rw [beurlingJHatEndpointRef_one]
      simp [beurlingJHat]
    · have hs0 : 0 < s := by linarith
      exact beurlingJHat_eq_endpointRef hs0 hslt
  · have hzero :
        ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici 1) 1 :=
      continuousWithinAt_const
    refine hzero.congr_of_eventuallyEq_of_mem ?_ (by simp)
    refine eventuallyEq_of_mem self_mem_nhdsWithin ?_
    intro s hs
    have hs_ge : 1 ≤ s := Set.mem_Ici.mp hs
    have hsabs : 1 ≤ |s| := by
      rw [abs_of_nonneg (by linarith [hs_ge] : 0 ≤ s)]
      exact hs_ge
    simp [beurlingJHat, not_lt.mpr hsabs]

theorem continuousAt_beurlingJHat_neg_one :
    ContinuousAt beurlingJHat (-1) := by
  have hcomp :
      ContinuousAt (fun s : ℝ => beurlingJHat (-s)) (-1) := by
    have hneg : ContinuousAt (fun s : ℝ => -s) (-1) :=
      continuous_neg.continuousAt
    have h1 : ContinuousAt beurlingJHat (-(-1 : ℝ)) := by
      rw [neg_neg]
      exact continuousAt_beurlingJHat_one
    exact h1.comp hneg
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with s
  exact (beurlingJHat_neg s).symm

theorem continuous_beurlingJHat :
    Continuous beurlingJHat := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy |t| 1 with ht | ht | ht
  · exact continuousAt_beurlingJHat_of_abs_lt_one ht
  · rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp ht with rfl | rfl
    · exact continuousAt_beurlingJHat_one
    · exact continuousAt_beurlingJHat_neg_one
  · exact continuousAt_beurlingJHat_of_one_lt_abs ht

end Probability
end CertifiedJL
