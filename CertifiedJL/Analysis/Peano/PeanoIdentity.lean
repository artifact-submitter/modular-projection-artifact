/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author.
-/

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Compact-support Peano identities

This generic probability/analysis module contains the deterministic compact-
support kernel and its law-level positive-part form.  The public compact law
identity is intentionally minimal: compact support makes the polynomial
boundary terms vanish without moment matching.  The later cutoff extension
will add the genuinely moment-matched noncompact P0 theorem, with explicit
first-moment integrability.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace CertifiedJL

private lemma hasCompactSupport_shift
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : HasCompactSupport f) (x : ℝ) :
    HasCompactSupport (fun t => f (x + t)) := by
  simpa [Function.comp_def] using
    hf.comp_isClosedEmbedding (Homeomorph.addLeft x).isClosedEmbedding

private lemma hasDerivAt_shift_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (x t : ℝ) :
    HasDerivAt (fun u => deriv f (x + u))
      (deriv (deriv f) (x + t)) t := by
  have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact (hdf.differentiable one_ne_zero (x + t)).hasDerivAt.comp_const_add x t

private lemma hasCompactSupport_shift_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : HasCompactSupport f) (x : ℝ) :
    HasCompactSupport (fun t => deriv f (x + t)) := by
  simpa [Function.comp_def] using
    hf.deriv.comp_isClosedEmbedding (Homeomorph.addLeft x).isClosedEmbedding

private lemma hasCompactSupport_shift_second_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : HasCompactSupport f) (x : ℝ) :
    HasCompactSupport (fun t => deriv (deriv f) (x + t)) := by
  simpa [Function.comp_def] using
    hf.deriv.deriv.comp_isClosedEmbedding (Homeomorph.addLeft x).isClosedEmbedding

/-
For a compactly supported `C²` function, the second derivative recovers the
function through the one-sided Peano kernel.  The endpoint is `y`, so the
kernel is `(y - t)` on `Iic y`; this is the sign convention used by (P0).
-/
theorem peanoKernel2_Iic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x y : ℝ) :
    f (x + y) =
      ∫ t in Iic y, (y - t) • deriv (deriv f) (x + t) := by
  let u : ℝ → E := fun t => deriv f (x + t)
  let v : ℝ → ℝ := fun t => y - t
  let u' : ℝ → E := fun t => deriv (deriv f) (x + t)
  have hu_cont : Continuous u := by
    dsimp [u]
    have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
    exact (hdf.fun_comp (contDiff_const.add contDiff_id)).continuous
  have hu'_cont : Continuous u' := by
    dsimp [u']
    have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
    have hshift : ContDiff ℝ 1 (fun t : ℝ => x + t) :=
      contDiff_const.add contDiff_id
    exact hdf.continuous_deriv_one.comp hshift.continuous
  have hv_cont : Continuous v := by
    dsimp [v]
    fun_prop
  have hu_comp : HasCompactSupport u := by
    exact hasCompactSupport_shift_deriv hfc x
  have hu'_comp : HasCompactSupport u' := by
    exact hasCompactSupport_shift_second_deriv hfc x
  have hu_v'_comp : HasCompactSupport
      ((fun _ : ℝ => (-1 : ℝ)) • u) := by
    exact hu_comp.smul_left
  have huv'_int : Integrable (v • u') := by
    apply (hv_cont.smul hu'_cont).integrable_of_hasCompactSupport
    exact hu'_comp.smul_left
  have hu_v'_int : Integrable ((fun _ : ℝ => (-1 : ℝ)) • u) := by
    apply (continuous_const.smul hu_cont).integrable_of_hasCompactSupport
    exact hu_v'_comp
  have huv'_sum_int : Integrable
      (v • u' + (fun _ : ℝ => (-1 : ℝ)) • u) :=
    huv'_int.add hu_v'_int
  have hderiv_u : ∀ t ∈ Iic y, HasDerivAt u (u' t) t := by
    intro t _
    exact hasDerivAt_shift_deriv hf x t
  have hderiv_v : ∀ t ∈ Iic y, HasDerivAt v (-1) t := by
    intro t _
    dsimp [v]
    simpa using (hasDerivAt_id' t).const_sub y
  have hderiv_prod : ∀ t ∈ Iic y,
      HasDerivAt (v • u) (v t • u' t + (-1 : ℝ) • u t) t := by
    intro t ht
    exact (hderiv_v t ht).smul (hderiv_u t ht)
  have hbot : Tendsto (v • u) atBot (𝓝 0) := by
    rw [hasCompactSupport_iff_eventuallyEq,
      Filter.coclosedCompact_eq_cocompact] at hu_comp
    have hu_zero : u =ᶠ[atBot] 0 := hu_comp.filter_mono atBot_le_cocompact
    have huv_zero : v • u =ᶠ[atBot] 0 := by
      filter_upwards [hu_zero] with t ht
      simp [ht]
    exact huv_zero.tendsto
  have hparts := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := y) (f := v • u)
    (f' := fun t => v t • u' t + (-1 : ℝ) • u t)
    hderiv_prod huv'_sum_int.integrableOn hbot
  have hparts' :
      ∫ t in Iic y, v t • u' t + (-1 : ℝ) • u t = 0 := by
    simpa [v] using hparts
  have hweighted :
      ∫ t in Iic y, v t • u' t = ∫ t in Iic y, u t := by
    have hsplit :
        (∫ t in Iic y, v t • u' t + (-1 : ℝ) • u t) =
          (∫ t in Iic y, v t • u' t) +
            ∫ t in Iic y, (-1 : ℝ) • u t := by
      exact integral_add huv'_int.integrableOn hu_v'_int.integrableOn
    rw [hsplit] at hparts'
    have hneg :
        (∫ t in Iic y, (-1 : ℝ) • u t) =
          -(∫ t in Iic y, u t) := by
      rw [integral_smul]
      simp
    rw [hneg] at hparts'
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hparts')
  have hshift_cont : ContDiff ℝ 1 (fun t => f (x + t)) := by
    exact hf.of_le (by norm_num) |>.fun_comp (contDiff_const.add contDiff_id)
  have hshift_comp : HasCompactSupport (fun t => f (x + t)) :=
    hasCompactSupport_shift hfc x
  have hfund := hshift_comp.integral_Iic_deriv_eq hshift_cont y
  have hfund' : (∫ t in Iic y, u t) = f (x + y) := by
    rw [show (fun t => deriv (fun s => f (x + s)) t) = u by
      funext t
      simp [u, deriv_comp_const_add]] at hfund
    simpa [u] using hfund
  simpa [u, u', v] using hfund'.symm.trans hweighted.symm

private lemma integral_Iic_weighted_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    {p p' : ℝ → ℝ} (hp : Continuous p) (hp' : Continuous p')
    (hderiv_p : ∀ t, HasDerivAt p (p' t) t) (y : ℝ) (hpy : p y = 0) :
    (∫ t in Iic y, p t • deriv g t) =
      -∫ t in Iic y, p' t • g t := by
  have hg_cont : Continuous g := hg.continuous
  have hg'_cont : Continuous (deriv g) := hg.continuous_deriv_one
  have hgc' : HasCompactSupport (deriv g) := hgc.deriv
  have hleft_int : Integrable (fun t => p t • deriv g t) := by
    apply (hp.smul hg'_cont).integrable_of_hasCompactSupport
    exact hgc'.smul_left
  have hright_int : Integrable (fun t => p' t • g t) := by
    apply (hp'.smul hg_cont).integrable_of_hasCompactSupport
    exact hgc.smul_left
  have hsum_int : Integrable
      (fun t => p t • deriv g t + p' t • g t) :=
    hleft_int.add hright_int
  have hderiv_prod : ∀ t ∈ Iic y,
      HasDerivAt (fun u => p u • g u)
        (p t • deriv g t + p' t • g t) t := by
    intro t _
    exact (hderiv_p t).smul ((hg.differentiable one_ne_zero t).hasDerivAt)
  have hbot : Tendsto (fun t => p t • g t) atBot (𝓝 0) := by
    have hgc0 := hgc
    rw [hasCompactSupport_iff_eventuallyEq,
      Filter.coclosedCompact_eq_cocompact] at hgc0
    have hg_zero : g =ᶠ[atBot] 0 := hgc0.filter_mono atBot_le_cocompact
    have hpg_zero : (fun t => p t • g t) =ᶠ[atBot] 0 := by
      filter_upwards [hg_zero] with t ht
      simp [ht]
    exact hpg_zero.tendsto
  have hparts := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := y) (f := fun t => p t • g t)
    (f' := fun t => p t • deriv g t + p' t • g t)
    hderiv_prod hsum_int.integrableOn hbot
  have hparts' :
      (∫ t in Iic y, p t • deriv g t + p' t • g t) = 0 := by
    simpa [hpy] using hparts
  have hsplit :
      (∫ t in Iic y, p t • deriv g t + p' t • g t) =
        (∫ t in Iic y, p t • deriv g t) +
          ∫ t in Iic y, p' t • g t := by
    exact integral_add hleft_int.integrableOn hright_int.integrableOn
  rw [hsplit] at hparts'
  exact eq_neg_of_add_eq_zero_left hparts'

theorem peanoKernel4_Iic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : ContDiff ℝ 4 f) (hfc : HasCompactSupport f)
    (x y : ℝ) :
    f (x + y) =
      ∫ t in Iic y, ((y - t) ^ 3 / 6) •
        deriv (deriv (deriv (deriv f))) (x + t) := by
  let g : ℝ → E := fun t => deriv (deriv (deriv f)) (x + t)
  have hg : ContDiff ℝ 1 g := by
    have hf3 : ContDiff ℝ 3 (deriv f) := hf.deriv'
    have hf2 : ContDiff ℝ 2 (deriv (deriv f)) := hf3.deriv'
    have hf1 : ContDiff ℝ 1 (deriv (deriv (deriv f))) := hf2.deriv'
    exact hf1.fun_comp (contDiff_const.add contDiff_id)
  have hgc : HasCompactSupport g := by
    simpa [g, Function.comp_def] using
      hfc.deriv.deriv.deriv.comp_isClosedEmbedding
        (Homeomorph.addLeft x).isClosedEmbedding
  have hfourth :
      (fun t => deriv g t) =
        (fun t => deriv (deriv (deriv (deriv f))) (x + t)) := by
    funext t
    dsimp [g]
    simp [deriv_comp_const_add]
  have hstep3 :
      (∫ t in Iic y, ((y - t) ^ 3 / 6) • deriv g t) =
        ∫ t in Iic y, ((y - t) ^ 2 / 2) • g t := by
    have hweighted := integral_Iic_weighted_deriv
      (g := g) hg hgc
      (p := fun t => (y - t) ^ 3 / 6)
      (p' := fun t => 3 * (y - t) ^ (3 - 1) * (-1) / 6)
      (by fun_prop) (by fun_prop)
      (by
        intro t
        simpa [div_eq_mul_inv] using
          (((hasDerivAt_id' t).const_sub y).pow 3 |>.div_const 6))
      y (by ring)
    apply hweighted.trans
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [← neg_smul]
    congr 1
    norm_num [pow_succ]
    ring
  have hstep2 :
      (∫ t in Iic y, ((y - t) ^ 2 / 2) • g t) =
        ∫ t in Iic y, (y - t) • deriv (deriv f) (x + t) := by
    have hweighted := integral_Iic_weighted_deriv
      (g := fun t => deriv (deriv f) (x + t))
      (by
        have hsecond : ContDiff ℝ 1 (deriv (deriv f)) :=
          (show ContDiff ℝ 2 (deriv (deriv f)) from
            (show ContDiff ℝ 3 (deriv f) from hf.deriv').deriv').of_le
            (by norm_num)
        exact hsecond.fun_comp (contDiff_const.add contDiff_id))
      (by
        simpa [Function.comp_def] using
          hfc.deriv.deriv.comp_isClosedEmbedding
            (Homeomorph.addLeft x).isClosedEmbedding)
      (p := fun t => (y - t) ^ 2 / 2)
      (p' := fun t => 2 * (y - t) ^ (2 - 1) * (-1) / 2)
      (by fun_prop) (by fun_prop)
      (by
        intro t
        simpa [div_eq_mul_inv] using
          (((hasDerivAt_id' t).const_sub y).pow 2 |>.div_const 2))
      y (by ring)
    have hderiv_second_shift :
        (fun t => deriv (fun s => deriv (deriv f) (x + s)) t) = g := by
      funext t
      simp [g, deriv_comp_const_add]
    calc
      (∫ t in Iic y, ((y - t) ^ 2 / 2) • g t) =
          ∫ t in Iic y, ((y - t) ^ 2 / 2) •
            deriv (fun s => deriv (deriv f) (x + s)) t := by
        apply integral_congr_ae
        filter_upwards [] with t
        have ht := congrFun hderiv_second_shift t
        rw [ht]
      _ = -∫ t in Iic y,
          (2 * (y - t) ^ (2 - 1) * (-1) / 2) •
            deriv (deriv f) (x + t) := hweighted
      _ = -∫ t in Iic y, -(y - t) • deriv (deriv f) (x + t) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        norm_num [pow_succ]
        ring
      _ = ∫ t in Iic y, (y - t) • deriv (deriv f) (x + t) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [neg_smul, neg_neg]
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  rw [peanoKernel2_Iic hf2 hfc x y]
  calc
    (∫ t in Iic y, (y - t) • deriv (deriv f) (x + t)) =
        ∫ t in Iic y, ((y - t) ^ 2 / 2) • g t := hstep2.symm
    _ = ∫ t in Iic y, ((y - t) ^ 3 / 6) • deriv g t := hstep3.symm
    _ = ∫ t in Iic y, ((y - t) ^ 3 / 6) •
        deriv (deriv (deriv (deriv f))) (x + t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have ht := congrFun hfourth t
      rw [ht]

/-- The degree-one stop-loss difference appearing in the second-order Peano
replacement. -/
noncomputable def firstStopLossDifference (μ ν : Measure ℝ) (t : ℝ) : ℝ :=
  (∫ y, max (y - t) 0 ∂μ) - ∫ y, max (y - t) 0 ∂ν

/-- The degree-three stop-loss difference appearing in the fourth-order P0. -/
noncomputable def cubicStopLossDifference (μ ν : Measure ℝ) (t : ℝ) : ℝ :=
  (∫ y, (max (y - t) 0) ^ 3 ∂μ) -
    (∫ y, (max (y - t) 0) ^ 3 ∂ν)

/-- The normalized k=4 replacement kernel is twice the stop-loss difference. -/
noncomputable def cubicStopLossKernel (μ ν : Measure ℝ) (t : ℝ) : ℝ :=
  2 * cubicStopLossDifference μ ν t

/--
The compact-support law-level fourth-order Peano identity.  Its explicit
`1/6` is the P0 Taylor prefactor; the later replacement kernel rewrites this
as `(1/12) * cubicStopLossKernel` after setting `k = 2 * Δ₃`.
-/
theorem peanoIdentity4_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {f : ℝ → E}
    (hf : ContDiff ℝ 4 f) (hfc : HasCompactSupport f) (x : ℝ)
    (hμKernel : Integrable
      (Function.uncurry (fun t y =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv f))) (x + t))) (volume.prod μ))
    (hνKernel : Integrable
      (Function.uncurry (fun t y =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv f))) (x + t))) (volume.prod ν))
    (hμRhs : Integrable (fun t =>
      (((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
        deriv (deriv (deriv (deriv f))) (x + t))))
    (hνRhs : Integrable (fun t =>
      (((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
        deriv (deriv (deriv (deriv f))) (x + t)))) :
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
      ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t) := by
  let K : ℝ → ℝ → E := fun t y =>
    ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
      deriv (deriv (deriv (deriv f))) (x + t)
  have hμKernel' : Integrable (Function.uncurry K) (volume.prod μ) := by
    simpa [K] using hμKernel
  have hνKernel' : Integrable (Function.uncurry K) (volume.prod ν) := by
    simpa [K] using hνKernel
  have hμsection : ∀ t,
      (∫ y, K t y ∂μ) =
        ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
          deriv (deriv (deriv (deriv f))) (x + t) := by
    intro t
    dsimp [K]
    calc
      (∫ y, ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv f))) (x + t) ∂μ) =
          (∫ y, (1 / 6 : ℝ) * (max (y - t) 0) ^ 3 ∂μ) •
            deriv (deriv (deriv (deriv f))) (x + t) :=
        integral_smul_const (fun y =>
          (1 / 6 : ℝ) * (max (y - t) 0) ^ 3)
          (deriv (deriv (deriv (deriv f))) (x + t))
      _ = ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
          deriv (deriv (deriv (deriv f))) (x + t) := by
        rw [integral_const_mul]
  have hνsection : ∀ t,
      (∫ y, K t y ∂ν) =
        ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
          deriv (deriv (deriv (deriv f))) (x + t) := by
    intro t
    dsimp [K]
    calc
      (∫ y, ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv f))) (x + t) ∂ν) =
          (∫ y, (1 / 6 : ℝ) * (max (y - t) 0) ^ 3 ∂ν) •
            deriv (deriv (deriv (deriv f))) (x + t) :=
        integral_smul_const (fun y =>
          (1 / 6 : ℝ) * (max (y - t) 0) ^ 3)
          (deriv (deriv (deriv (deriv f))) (x + t))
      _ = ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
          deriv (deriv (deriv (deriv f))) (x + t) := by
        rw [integral_const_mul]
  have hset : ∀ y,
      (∫ t, K t y) =
        ∫ t in Iic y, ((y - t) ^ 3 / 6) •
          deriv (deriv (deriv (deriv f))) (x + t) := by
    intro y
    rw [← integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ≤ y
    · simp [K, ht, div_eq_mul_inv]
      ring_nf
    · have hty : y - t ≤ 0 := sub_nonpos.mpr (le_of_not_ge ht)
      simp [K, ht, max_eq_right hty]
  have hμswap :
      (∫ t, (∫ y, K t y ∂μ)) = ∫ y, f (x + y) ∂μ := by
    rw [integral_integral_swap hμKernel']
    apply integral_congr_ae
    filter_upwards [] with y
    exact (hset y).trans (peanoKernel4_Iic hf hfc x y).symm
  have hνswap :
      (∫ t, (∫ y, K t y ∂ν)) = ∫ y, f (x + y) ∂ν := by
    rw [integral_integral_swap hνKernel']
    apply integral_congr_ae
    filter_upwards [] with y
    exact (hset y).trans (peanoKernel4_Iic hf hfc x y).symm
  have hμK_eq :
      (∫ t, ∫ y, K t y ∂μ) =
        ∫ t, ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
          deriv (deriv (deriv (deriv f))) (x + t) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => hμsection t)
  have hνK_eq :
      (∫ t, ∫ y, K t y ∂ν) =
        ∫ t, ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
          deriv (deriv (deriv (deriv f))) (x + t) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => hνsection t)
  rw [← hμswap, ← hνswap, hμK_eq, hνK_eq]
  calc
    (∫ t, ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
        deriv (deriv (deriv (deriv f))) (x + t)) -
        ∫ t, ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
          deriv (deriv (deriv (deriv f))) (x + t) =
      ∫ t, (((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
        deriv (deriv (deriv (deriv f))) (x + t) -
        ((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
          deriv (deriv (deriv (deriv f))) (x + t)) :=
      (integral_sub hμRhs hνRhs).symm
    _ = ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp [cubicStopLossDifference]
        rw [← sub_smul]
        congr 1
        ring)

private lemma peanoKernel2_full
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x y : ℝ) :
    f (x + y) =
      ∫ t, max (y - t) 0 • deriv (deriv f) (x + t) := by
  have hsecond_cont : Continuous (fun t => deriv (deriv f) (x + t)) := by
    have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
    have hshift : ContDiff ℝ 1 (fun t : ℝ => x + t) :=
      contDiff_const.add contDiff_id
    exact hdf.continuous_deriv_one.comp hshift.continuous
  have hsecond_comp : HasCompactSupport
      (fun t => deriv (deriv f) (x + t)) := by
    simpa [Function.comp_def] using
      hfc.deriv.deriv.comp_isClosedEmbedding (Homeomorph.addLeft x).isClosedEmbedding
  have hpos_cont : Continuous (fun t => max (y - t) 0) := by
    fun_prop
  have hkernel_int : Integrable
      (fun t => max (y - t) 0 • deriv (deriv f) (x + t)) := by
    apply (hpos_cont.smul hsecond_cont).integrable_of_hasCompactSupport
    exact hsecond_comp.smul_left
  have hset :
      (∫ t in Iic y, (y - t) • deriv (deriv f) (x + t)) =
        ∫ t, max (y - t) 0 • deriv (deriv f) (x + t) := by
    rw [← integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ≤ y
    · simp [ht]
    · have hty : y - t ≤ 0 := sub_nonpos.mpr (le_of_not_ge ht)
      simp [ht, max_eq_right hty]
  exact (peanoKernel2_Iic hf hfc x y).trans hset

/--
The minimal compact-support k=2 law identity.  Compact support makes the
one-sided representation valid for each law separately, so no moment-matching
premise is needed here.  The later noncompact cutoff theorem adds equal mass,
integrable first moments, and the actual polynomial cancellation.
-/
theorem peanoIdentity2_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {f : ℝ → E}
    (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : ℝ)
    (hμKernel : Integrable
      (Function.uncurry (fun t y =>
        max (y - t) 0 • deriv (deriv f) (x + t))) (volume.prod μ))
    (hνKernel : Integrable
      (Function.uncurry (fun t y =>
        max (y - t) 0 • deriv (deriv f) (x + t))) (volume.prod ν))
    (hμRhs : Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂μ) • deriv (deriv f) (x + t)))
    (hνRhs : Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂ν) • deriv (deriv f) (x + t))) :
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
      ∫ t, ((∫ y, max (y - t) 0 ∂μ) -
        (∫ y, max (y - t) 0 ∂ν)) • deriv (deriv f) (x + t) := by
  let K : ℝ → ℝ → E := fun t y =>
    max (y - t) 0 • deriv (deriv f) (x + t)
  have hμKernel' : Integrable (Function.uncurry K) (volume.prod μ) := by
    simpa [K] using hμKernel
  have hνKernel' : Integrable (Function.uncurry K) (volume.prod ν) := by
    simpa [K] using hνKernel
  have hμsection : ∀ t,
      (∫ y, K t y ∂μ) =
        (∫ y, max (y - t) 0 ∂μ) • deriv (deriv f) (x + t) := by
    intro t
    dsimp [K]
    exact integral_smul_const (fun y => max (y - t) 0)
      (deriv (deriv f) (x + t))
  have hνsection : ∀ t,
      (∫ y, K t y ∂ν) =
        (∫ y, max (y - t) 0 ∂ν) • deriv (deriv f) (x + t) := by
    intro t
    dsimp [K]
    exact integral_smul_const (fun y => max (y - t) 0)
      (deriv (deriv f) (x + t))
  have hμswap :
      (∫ t, (∫ y, K t y ∂μ) ∂volume) = ∫ y, f (x + y) ∂μ := by
    rw [integral_integral_swap hμKernel']
    apply integral_congr_ae
    filter_upwards [] with y
    simpa [K] using (peanoKernel2_full hf hfc x y).symm
  have hνswap :
      (∫ t, (∫ y, K t y ∂ν) ∂volume) = ∫ y, f (x + y) ∂ν := by
    rw [integral_integral_swap hνKernel']
    apply integral_congr_ae
    filter_upwards [] with y
    simpa [K] using (peanoKernel2_full hf hfc x y).symm
  have hμK_eq :
      (∫ t, ∫ y, K t y ∂μ) =
        ∫ t, (∫ y, max (y - t) 0 ∂μ) • deriv (deriv f) (x + t) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => hμsection t)
  have hνK_eq :
      (∫ t, ∫ y, K t y ∂ν) =
        ∫ t, (∫ y, max (y - t) 0 ∂ν) • deriv (deriv f) (x + t) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => hνsection t)
  rw [← hμswap, ← hνswap, hμK_eq, hνK_eq]
  calc
    (∫ t, (∫ y, max (y - t) 0 ∂μ) • deriv (deriv f) (x + t)) -
        ∫ t, (∫ y, max (y - t) 0 ∂ν) • deriv (deriv f) (x + t) =
        ∫ t, ((∫ y, max (y - t) 0 ∂μ) • deriv (deriv f) (x + t) -
          (∫ y, max (y - t) 0 ∂ν) • deriv (deriv f) (x + t)) :=
      (integral_sub hμRhs hνRhs).symm
    _ = ∫ t, ((∫ y, max (y - t) 0 ∂μ) -
        (∫ y, max (y - t) 0 ∂ν)) • deriv (deriv f) (x + t) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => (sub_smul _ _ _).symm)

end CertifiedJL
