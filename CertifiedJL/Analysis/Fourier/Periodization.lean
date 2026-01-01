/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Probability.Finite.Experiment
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Centered modular periodization

The first theorem is pointwise and keeps every integer image in the series.
The second theorem performs the expectation/series exchange with Tonelli in
the extended-real layer, which is the explicit bridge needed before any later
real-valued Gaussian estimates.
-/

open scoped ENNReal

open MeasureTheory

namespace CertifiedJL

/--
The centered Gaussian kernel is bounded by the complete integer-image sum.
The representative term is selected from the exact `ZMod` congruence, so the
inequality includes all nonzero images rather than only the nearest one.
-/
theorem centeredPeriodization_pointwise
    {q : ℕ} (hq : Odd q) (z : ℤ) (s : ℝ) (_hs : 0 < s) :
    ENNReal.ofReal
        (Real.exp (-s * (centeredMod q z : ℝ) ^ 2)) ≤
      ∑' n : ℤ,
        ENNReal.ofReal
          (Real.exp (-s * ((z : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) := by
  have hq0 : q ≠ 0 := by
    intro hzero
    subst q
    exact Nat.not_odd_zero hq
  let : NeZero q := ⟨hq0⟩
  have hcong :
      (centeredMod q z : ZMod q) = (z : ZMod q) :=
    centeredMod_intCast q z
  have hdiv : (q : ℤ) ∣ z - centeredMod q z := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      (centeredMod q z) z q).mp hcong
  rcases hdiv with ⟨n, hn⟩
  have hterm :
      (z : ℝ) - (n : ℝ) * (q : ℝ) = (centeredMod q z : ℝ) := by
    have hn' :
        (z : ℝ) - (centeredMod q z : ℝ) =
          (q : ℝ) * (n : ℝ) := by
      exact_mod_cast hn
    linarith
  calc
    ENNReal.ofReal
          (Real.exp (-s * (centeredMod q z : ℝ) ^ 2)) =
        ENNReal.ofReal
          (Real.exp (-s * ((z : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) := by
      rw [hterm]
    _ ≤ ∑' k : ℤ,
        ENNReal.ofReal
          (Real.exp (-s * ((z : ℝ) - (k : ℝ) * (q : ℝ)) ^ 2)) := by
      exact ENNReal.le_tsum n

/--
Tonelli exchanges a finite-PMF expectation with the full modular-image sum.
The pointwise theorem is kept as a separate premise in the proof chain so
the measure-theoretic exchange and the modular representative argument remain
auditable independently.
-/
theorem centeredPeriodization_tonelli_eq
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (p : PMF Ω) {q : ℕ} (T : Ω → ℤ) (hT : Measurable T)
    (s : ℝ) :
    ∫⁻ ω, ∑' n : ℤ,
        ENNReal.ofReal
          (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂p.toMeasure =
      ∑' n : ℤ, ∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂p.toMeasure := by
  apply lintegral_tsum
  intro n
  have hz : Measurable (fun z : ℤ => ENNReal.ofReal
      (Real.exp (-s * ((z : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2))) :=
    measurable_of_countable _
  exact (hz.comp hT).aemeasurable

theorem centeredPeriodization_tonelli
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (p : PMF Ω) {q : ℕ} (hq : Odd q) (T : Ω → ℤ)
    (hT : Measurable T)
    (s : ℝ) (hs : 0 < s) :
    ∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-s * (centeredMod q (T ω) : ℝ) ^ 2)) ∂p.toMeasure ≤
      ∑' n : ℤ, ∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂p.toMeasure := by
  have hpointwise (ω : Ω) :
      ENNReal.ofReal
          (Real.exp (-s * (centeredMod q (T ω) : ℝ) ^ 2)) ≤
        ∑' n : ℤ,
          ENNReal.ofReal
            (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) :=
    centeredPeriodization_pointwise hq (T ω) s hs
  calc
    ∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-s * (centeredMod q (T ω) : ℝ) ^ 2)) ∂p.toMeasure ≤
        ∫⁻ ω, ∑' n : ℤ,
          ENNReal.ofReal
            (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂p.toMeasure := by
      exact lintegral_mono hpointwise
    _ = ∑' n : ℤ, ∫⁻ ω,
          ENNReal.ofReal
            (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂p.toMeasure := by
      exact centeredPeriodization_tonelli_eq p T hT s

/-- Split Tonelli periodization at the literal zero image while allowing a
consumer to supply separate bounds for every nonzero orientation. -/
theorem centeredPeriodization_tonelli_nonzero
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (p : PMF Ω) {q : ℕ} (hq : Odd q) (T : Ω → ℤ)
    (hT : Measurable T) (s : ℝ) (hs : 0 < s)
    (g : ℤ → ℝ≥0∞)
    (hg : ∀ n : ℤ, n ≠ 0 →
      ∫⁻ ω, ENNReal.ofReal
          (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2))
          ∂p.toMeasure ≤ g n) :
    ∫⁻ ω, ENNReal.ofReal
        (Real.exp (-s * (centeredMod q (T ω) : ℝ) ^ 2)) ∂p.toMeasure ≤
      (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-s * (T ω : ℝ) ^ 2)) ∂p.toMeasure) +
      ∑' n : ℤ, if n = 0 then 0 else g n := by
  let image : ℤ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ENNReal.ofReal
      (Real.exp (-s * ((T ω : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂p.toMeasure
  have htail :
      (∑' n : ℤ, if n = 0 then 0 else image n) ≤
        ∑' n : ℤ, if n = 0 then 0 else g n := by
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simpa [hn, image] using hg n hn
  calc
    ∫⁻ ω, ENNReal.ofReal
        (Real.exp (-s * (centeredMod q (T ω) : ℝ) ^ 2)) ∂p.toMeasure ≤
        ∑' n : ℤ, image n := by
      simpa [image] using centeredPeriodization_tonelli p hq T hT s hs
    _ = image 0 + ∑' n : ℤ, if n = 0 then 0 else image n := by
      rw [ENNReal.tsum_eq_add_tsum_ite (f := image) 0]
      congr 1
      apply tsum_congr
      intro n
      split_ifs <;> rfl
    _ ≤ image 0 + ∑' n : ℤ, if n = 0 then 0 else g n :=
      add_le_add le_rfl htail
    _ = (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-s * (T ω : ℝ) ^ 2)) ∂p.toMeasure) +
        ∑' n : ℤ, if n = 0 then 0 else g n := by
      simp [image]

end CertifiedJL
