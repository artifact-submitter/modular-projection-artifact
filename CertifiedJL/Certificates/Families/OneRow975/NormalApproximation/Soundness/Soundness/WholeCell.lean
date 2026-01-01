/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Quadrature.EndpointRiemann
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Soundness.Product

/-!
# Whole-cell soundness for the moderate-Lyapunov certificate
-/

open MeasureTheory Set
open scoped BigOperators

namespace CertifiedJL
namespace TyurinModerate

open Probability

private theorem mul_le_intervalUpper
    {I J : DInterval} {x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ (I.upperRat : ℝ))
    (hy : y ≤ (J.upperRat : ℝ)) :
    x * y ≤ ((I * J).upperRat : ℝ) := by
  have hI0 : 0 ≤ (I.upperRat : ℝ) := hx0.trans hx
  have hJ0 : 0 ≤ (J.upperRat : ℝ) := hy0.trans hy
  exact (mul_le_mul hx hy hy0 hI0).trans
    (Interval.upperRat_mul_upperRat_le I J)

private theorem coreUInterval_contains
    {C : Cell} {i : ℕ} {u : ℝ}
    (hu : (C.cutoff : ℝ) * i / C.coreCells ≤ u ∧
      u ≤ (C.cutoff : ℝ) * (i + 1) / C.coreCells) :
    (coreUInterval C i).Contains u := by
  unfold coreUInterval
  apply Interval.contains_enclose
  exact_mod_cast hu

private theorem outerXInterval_contains
    {C : Cell} {i : ℕ} {x : ℝ}
    (hx :
      (2 * C.hi * C.cutoff : ℚ) +
          (2 * C.hi * C.bandwidth -
            2 * C.hi * C.cutoff) * i / C.outerCells ≤ x ∧
      x ≤
        (2 * C.hi * C.cutoff : ℚ) +
          (2 * C.hi * C.bandwidth -
            2 * C.hi * C.cutoff) * (i + 1) /
              C.outerCells) :
    (outerXInterval C i).Contains (x : ℝ) := by
  unfold outerXInterval
  dsimp only
  apply Interval.contains_enclose
  exact_mod_cast hx

private theorem endpoint_deltaOne_upper
    {L b t : ℝ} (hL0 : 0 ≤ L) (hLb : L ≤ b) :
    tyurinDeltaOne L t ≤
      tyurinDeltaOneTrapezoidUpper innerTrapezoids b t := by
  have htrap :=
    tyurinDeltaOne_le_trapezoidUpper
      (n := innerTrapezoids) (t := t)
      (by norm_num [innerTrapezoids]) hL0
  apply htrap.trans
  unfold tyurinDeltaOneTrapezoidUpper
  have hfactor :
      0 ≤ Real.exp (-(|t| ^ 2) / 2) *
        sqExpSqTrapezoid innerTrapezoids 1 |t| := by
    exact mul_nonneg (Real.exp_nonneg _)
      (sqExpSqTrapezoid_nonneg
        (by norm_num [innerTrapezoids]) (abs_nonneg _))
  nlinarith

private theorem endpoint_deltaMin_upper
    {C : Cell} {L t : ℝ}
    (hL : 0 < L) (hLb : L ≤ (C.hi : ℝ)) :
    min (tyurinDeltaOne L t) (tyurinDeltaTwo L t) ≤
      min
        (tyurinDeltaOneTrapezoidUpper
          innerTrapezoids (C.hi : ℝ) t)
        (tyurinDeltaTwoTrapezoidUpper
          innerTrapezoids (C.hi : ℝ) t) :=
  min_le_min
    (endpoint_deltaOne_upper hL.le hLb)
    (tyurinDeltaTwo_le_endpointTrapezoid
      (n := innerTrapezoids)
      (by norm_num [innerTrapezoids]) hL hLb)

private theorem chosenDelta_contains_and_upper
    {C : Cell} {L t : ℝ} {TI : DInterval}
    (choice : DeltaChoice)
    (hL : 0 < L) (hLb : L ≤ (C.hi : ℝ))
    (ht : TI.Contains t) (ht0 : 0 ≤ t)
    (hgeometry : geometryCheck C = true)
    (hsafe : chosenDeltaSafe C TI choice = true) :
    ∃ d : ℝ,
      (chosenDelta C TI choice).Contains d ∧
      min (tyurinDeltaOne L t) (tyurinDeltaTwo L t) ≤ d := by
  cases choice with
  | one =>
      let d :=
        tyurinDeltaOneTrapezoidUpper
          innerTrapezoids (C.hi : ℝ) t
      refine ⟨d, ?_, ?_⟩
      · exact deltaOne_contains_endpointTrapezoid
          ht ht0 (by simpa [chosenDeltaSafe] using hsafe)
      · exact (min_le_left _ _).trans
          (endpoint_deltaOne_upper hL.le hLb)
  | two =>
      let d :=
        tyurinDeltaTwoTrapezoidUpper
          innerTrapezoids (C.hi : ℝ) t
      refine ⟨d, ?_, ?_⟩
      · exact deltaTwo_contains_endpointTrapezoid
          ht ht0 hgeometry
          (by simpa [chosenDeltaSafe] using hsafe)
      · exact (min_le_right _ _).trans
          (tyurinDeltaTwo_le_endpointTrapezoid
            (n := innerTrapezoids)
            (by norm_num [innerTrapezoids]) hL hLb)

private theorem chosenKernel_upper
    {C : Cell} {t : ℝ} {TI : DInterval}
    (choice : KernelChoice)
    (ht : TI.Contains t) (ht0 : 0 < t)
    (htU : t ≤ (C.bandwidth : ℝ))
    (hgeometry : geometryCheck C = true)
    (hsafe : chosenKernelSafe C TI choice = true) :
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) t‖ ≤
      ((chosenKernel C TI choice).upperRat : ℝ) := by
  have hUpos : (0 : ℝ) < C.bandwidth := by
    rcases geometryCheck_sound hgeometry with
      ⟨_hlo, _hlohi, _hratio, hcutoff, hcut, _⟩
    exact_mod_cast hcutoff.trans_le hcut
  have hcertificate :=
    norm_scaledPrawitzKernel_le_certificateEnvelope
      hUpos ht0.ne' (by simpa [abs_of_pos ht0] using htU)
  cases choice with
  | i29 =>
      have henvelope :
          scaledPrawitzCertificateEnvelope
              (C.bandwidth : ℝ) t ≤
            scaledPrawitzI29Envelope t := by
        unfold scaledPrawitzCertificateEnvelope
        split_ifs
        · exact min_le_left _ _
        · exact le_rfl
      exact hcertificate.trans <|
        henvelope.trans <|
          kernelI29_upper ht ht0
            (by
              simpa [chosenKernelSafe] using
                of_decide_eq_true hsafe)
  | endpoint =>
      unfold chosenKernelSafe at hsafe
      rw [Bool.and_eq_true] at hsafe
      have hhalfCheck :
          C.bandwidth / 2 ≤ TI.lowerRat :=
        of_decide_eq_true hsafe.1
      have hhalf :
          (C.bandwidth : ℝ) / 2 ≤ |t| := by
        rw [abs_of_pos ht0]
        have hcast :
            ((C.bandwidth / 2 : ℚ) : ℝ) ≤
              (TI.lowerRat : ℝ) := by
          exact_mod_cast hhalfCheck
        have hcast' :
            (C.bandwidth : ℝ) / 2 ≤
              (TI.lowerRat : ℝ) := by simpa using hcast
        exact hcast'.trans (lowerRat_le_of_contains ht)
      have henvelope :
          scaledPrawitzCertificateEnvelope
              (C.bandwidth : ℝ) t ≤
            scaledPrawitzEndpointEnvelope
              (C.bandwidth : ℝ) t := by
        unfold scaledPrawitzCertificateEnvelope
        rw [if_pos hhalf]
        exact min_le_right _ _
      exact hcertificate.trans <|
        henvelope.trans <|
          kernelEndpoint_upper ht ht0.le hgeometry htU

private theorem coreIntegrand_upper_of_pos
    {C : Cell} {L u : ℝ} {i : ℕ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hi0 : 0 < i) (hi : i < C.coreCells)
    (hu :
      (C.cutoff : ℝ) * i / C.coreCells ≤ u ∧
      u ≤ (C.cutoff : ℝ) * (i + 1) / C.coreCells)
    (hsafe : coreIntegrandSafe C i = true) :
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      ((coreIntegrand C i).upperRat : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, _hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, _hfourL,
      hcore, _houter, _hband⟩
  have hloReal : (0 : ℝ) < C.lo := by
    exact_mod_cast hlo
  have hLpos : 0 < L := hloReal.trans_le hL
  have hUpos : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hnpos : (0 : ℝ) < C.coreCells := by
    have := (geometryCheck_sound hgeometry)
    rcases this with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcore, _⟩
    exact_mod_cast hcore
  have hcutReal : (0 : ℝ) < C.cutoff := by
    exact_mod_cast hcutoff
  have hu0 : 0 < u := by
    have hiReal : (0 : ℝ) < i := by exact_mod_cast hi0
    have : 0 < (C.cutoff : ℝ) * i / C.coreCells := by
      positivity
    exact this.trans_le hu.1
  have huCut : u ≤ (C.cutoff : ℝ) := by
    have hiSucc : (i + 1 : ℝ) ≤ C.coreCells := by
      exact_mod_cast hi
    calc
      u ≤ (C.cutoff : ℝ) * (i + 1) / C.coreCells := hu.2
      _ ≤ (C.cutoff : ℝ) := by
        rw [div_le_iff₀ hnpos]
        exact mul_le_mul_of_nonneg_left hiSucc hcutReal.le
  have huU : u ≤ (C.bandwidth : ℝ) :=
    huCut.trans (by exact_mod_cast hcut)
  unfold coreIntegrandSafe at hsafe
  dsimp only at hsafe
  simp only [Bool.and_eq_true] at hsafe
  let TI := coreUInterval C i
  have hTI : TI.Contains u :=
    coreUInterval_contains hu
  let d : ℝ :=
    min
      (tyurinDeltaOneTrapezoidUpper
        innerTrapezoids (C.hi : ℝ) u)
      (tyurinDeltaTwoTrapezoidUpper
        innerTrapezoids (C.hi : ℝ) u)
  have hdContains :
      (deltaMin C TI).Contains d := by
    exact deltaMin_contains_endpointTrapezoids
      hTI hu0.le hgeometry hsafe.1.2 hsafe.2
  have hactualD :
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤ d :=
    endpoint_deltaMin_upper hLpos hLb
  have hactualD0 :
      0 ≤ min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) :=
    le_min (tyurinDeltaOne_nonneg hLpos.le)
      (tyurinDeltaTwo_nonneg hLpos)
  have hd0 : 0 ≤ d := hactualD0.trans hactualD
  have hkernelEnvelope :=
    kernel_upper hTI hu0 huU hgeometry hsafe.1.1
  have hkernel :
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ ≤
        ((kernel C TI).upperRat : ℝ) :=
    (norm_scaledPrawitzKernel_le_certificateEnvelope
      hUpos hu0.ne' (by simpa [abs_of_pos hu0] using huU)).trans
      hkernelEnvelope
  have hproduct :
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ * d ≤
        ((kernel C TI * deltaMin C TI).upperRat : ℝ) :=
    mul_le_intervalUpper (norm_nonneg _) hd0
      hkernel (le_upperRat hdContains)
  unfold coreIntegrand
  dsimp only [TI] at hproduct ⊢
  exact (mul_le_mul_of_nonneg_left hactualD
    (norm_nonneg _)).trans hproduct

/--
One stored kernel choice and one stored discrepancy choice bound the actual
core integrand without evaluating the discarded alternatives.
-/
theorem chosenCoreIntegrand_upper_of_pos
    {C : Cell} {L u : ℝ} {i : ℕ}
    (choice : CoreChoice)
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hi0 : 0 < i) (hi : i < C.coreCells)
    (hu :
      (C.cutoff : ℝ) * i / C.coreCells ≤ u ∧
      u ≤ (C.cutoff : ℝ) * (i + 1) / C.coreCells)
    (hsafe : chosenCoreIntegrandSafe C choice i = true) :
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      ((chosenCoreIntegrand C choice i).upperRat : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, _hratio, hcutoff, hcut, _hbandlo,
      _hrootLo, _hrootLoCube, _hrootHi, _hrootHiCube,
      _hrootInterval, _hhiInterval, _htwoHiInterval,
      _htwoHiRatInterval, _hfourLyapunov, hcore, _⟩
  have hloReal : (0 : ℝ) < C.lo := by exact_mod_cast hlo
  have hLpos : 0 < L := hloReal.trans_le hL
  have hnpos : (0 : ℝ) < C.coreCells := by
    exact_mod_cast hcore
  have hu0 : 0 < u := by
    have hiReal : (0 : ℝ) < i := by exact_mod_cast hi0
    have hcutoffReal : (0 : ℝ) < C.cutoff := by
      exact_mod_cast hcutoff
    have : 0 < (C.cutoff : ℝ) * i / C.coreCells := by
      positivity
    exact this.trans_le hu.1
  have huCut : u ≤ (C.cutoff : ℝ) := by
    have hiSucc : (i + 1 : ℝ) ≤ C.coreCells := by
      exact_mod_cast hi
    calc
      u ≤ (C.cutoff : ℝ) * (i + 1) / C.coreCells := hu.2
      _ ≤ (C.cutoff : ℝ) := by
        rw [div_le_iff₀ hnpos]
        exact mul_le_mul_of_nonneg_left hiSucc
          (by exact_mod_cast hcutoff.le)
  have huU : u ≤ (C.bandwidth : ℝ) :=
    huCut.trans (by exact_mod_cast hcut)
  unfold chosenCoreIntegrandSafe at hsafe
  rw [Bool.and_eq_true] at hsafe
  let TI := coreUInterval C i
  have hTI : TI.Contains u := coreUInterval_contains hu
  obtain ⟨d, hdContains, hactualD⟩ :=
    chosenDelta_contains_and_upper choice.delta
      hLpos hLb hTI hu0.le hgeometry hsafe.2
  have hactualD0 :
      0 ≤ min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) :=
    le_min (tyurinDeltaOne_nonneg hLpos.le)
      (tyurinDeltaTwo_nonneg hLpos)
  have hd0 : 0 ≤ d := hactualD0.trans hactualD
  have hkernel :=
    chosenKernel_upper choice.kernel hTI hu0 huU
      hgeometry hsafe.1
  have hproduct :
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ * d ≤
        ((chosenKernel C TI choice.kernel *
          chosenDelta C TI choice.delta).upperRat : ℝ) :=
    mul_le_intervalUpper (norm_nonneg _) hd0
      hkernel (le_upperRat hdContains)
  unfold chosenCoreIntegrand
  dsimp only [TI] at hproduct ⊢
  exact (mul_le_mul_of_nonneg_left hactualD
    (norm_nonneg _)).trans hproduct

private theorem firstCore_upper
    {C : Cell} {L u : ℝ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hu0 : 0 ≤ u)
    (hu1 : u ≤ (C.cutoff : ℝ) / C.coreCells) :
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      ((firstCoreUpper C).upperRat : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, _hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, _hfourL, hcore, _⟩
  have hLpos : 0 < L := by
    have : (0 : ℝ) < C.lo := by exact_mod_cast hlo
    exact this.trans_le hL
  have hnpos : (0 : ℝ) < C.coreCells := by
    exact_mod_cast hcore
  have hTpos :
      0 < (C.cutoff : ℝ) / C.coreCells := by
    have : (0 : ℝ) < C.cutoff := by exact_mod_cast hcutoff
    positivity
  have hUpos : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hTU :
      (C.cutoff : ℝ) / C.coreCells ≤
        (C.bandwidth : ℝ) := by
    have hone : (1 : ℝ) ≤ C.coreCells := by
      exact_mod_cast hcore
    calc
      (C.cutoff : ℝ) / C.coreCells ≤ C.cutoff := by
        rw [div_le_iff₀ hnpos]
        nlinarith [show (0 : ℝ) < C.cutoff by exact_mod_cast hcutoff]
      _ ≤ C.bandwidth := by exact_mod_cast hcut
  have hactual :=
    tyurinCoreIntegrand_le_trapezoidCertificate
      (n := innerTrapezoids)
      (by norm_num [innerTrapezoids]) hLpos hUpos hu0
      (hu1.trans hTU)
  have hcert :=
    tyurinCoreTrapezoidCertificateIntegrand_le
      (n := innerTrapezoids)
      (by norm_num [innerTrapezoids]) hLpos hTpos hUpos hTU
      hu0 hu1
  have hbound :
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
        (513 / 500 : ℝ) * (C.hi : ℝ) *
          ((C.cutoff : ℝ) / C.coreCells) ^ 2 / 4 := by
    calc
      _ ≤ tyurinCoreTrapezoidCertificateIntegrand
          innerTrapezoids L (C.bandwidth : ℝ) u := hactual
      _ ≤ (513 / 500 : ℝ) * L *
          ((C.cutoff : ℝ) / C.coreCells) ^ 2 / 4 := hcert
      _ ≤ (513 / 500 : ℝ) * (C.hi : ℝ) *
          ((C.cutoff : ℝ) / C.coreCells) ^ 2 / 4 := by
        gcongr
  have hcontains :
      (firstCoreUpper C).Contains
        ((513 / 500 : ℝ) * (C.hi : ℝ) *
          ((C.cutoff : ℝ) / C.coreCells) ^ 2 / 4) := by
    unfold firstCoreUpper
    have hfront :
        (rat (513 / 500) * C.lyapunovInterval).Contains
          ((513 / 500 : ℝ) * (C.hi : ℝ)) :=
      Interval.contains_mul
        (by simpa using contains_rat (513 / 500))
        (by simpa [Cell.lyapunovInterval] using contains_rat C.hi)
    have hT :
        (rat (C.cutoff / C.coreCells)).Contains
          ((C.cutoff : ℝ) / C.coreCells) := by
      simpa using contains_rat (C.cutoff / C.coreCells)
    have hfrontSq :=
      Interval.contains_mul hfront (Interval.contains_square hT)
    simpa [div_eq_mul_inv, mul_assoc] using
      Interval.contains_mul hfrontSq
        (by simpa using contains_rat (1 / 4))
  exact hbound.trans (le_upperRat hcontains)

private theorem outerUInterval_contains
    {C : Cell} {i : ℕ} {u : ℝ}
    (hx : (outerXInterval C i).Contains
      (2 * (C.hi : ℝ) * u))
    (hgeometry : geometryCheck C = true) :
    (outerUInterval C i).Contains u := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, _hcutoff, _hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, htwoExact, _⟩
  have hden :
      (rat (2 * C.hi)).Contains (2 * (C.hi : ℝ)) := by
    simpa using contains_rat (2 * C.hi)
  have hquot := contains_div htwoExact hx hden
  have hhi : (C.hi : ℝ) ≠ 0 := by
    have : 0 < C.hi :=
      (geometryCheck_sound hgeometry).1.trans_le
        (geometryCheck_sound hgeometry).2.1
    exact_mod_cast this.ne'
  unfold outerUInterval
  convert hquot using 1
  field_simp

private theorem outerScaledIntegrand_upper
    {C : Cell} {L u : ℝ} {i : ℕ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (huCut : (C.cutoff : ℝ) ≤ u)
    (huU : u ≤ (C.bandwidth : ℝ))
    (hx : (outerXInterval C i).Contains
      (2 * (C.hi : ℝ) * u))
    (hband : 2 * (C.hi : ℝ) * u ≤ 157 / 25)
    (hsafe : outerScaledIntegrandSafe C i = true) :
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        tyurinProductEnvelope L u /
          (2 * (C.hi : ℝ)) ≤
      ((outerScaledIntegrand C i).upperRat : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, htwoExact, _⟩
  have ha : (0 : ℝ) < C.lo := by exact_mod_cast hlo
  have hLpos : 0 < L := ha.trans_le hL
  have hb : (0 : ℝ) < C.hi := hLpos.trans_le hLb
  have hUpos : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hu0 : 0 ≤ u := by
    have : (0 : ℝ) < C.cutoff := by exact_mod_cast hcutoff
    exact this.le.trans huCut
  have huPos : 0 < u := by
    have : (0 : ℝ) < C.cutoff := by exact_mod_cast hcutoff
    exact this.trans_le huCut
  unfold outerScaledIntegrandSafe at hsafe
  rw [Bool.and_eq_true] at hsafe
  have huI := outerUInterval_contains hx hgeometry
  have hk :=
    (norm_scaledPrawitzKernel_le_certificateEnvelope
      hUpos huPos.ne'
      (by simpa [abs_of_nonneg hu0] using huU)).trans
      (kernel_upper huI huPos huU hgeometry hsafe.1)
  have hpCell :=
    tyurinProductEnvelope_le_cellEndpoint
      ha hL hLb hu0 (by
        have hcast :
            (((C.hi / C.lo : ℚ) : ℝ)) ≤
              (((471 / 400 : ℚ) : ℝ)) := by
          exact_mod_cast hratio
        simpa using hcast) hband
  have hpUpper :=
    productEnvelope_upper hx hband hgeometry hsafe.2
  have hp0 := tyurinProductEnvelope_nonneg L u
  have hcell0 := tyurinProductEnvelope_nonneg (C.hi : ℝ) u
  have hkp :
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          tyurinProductEnvelope L u ≤
        ((kernel C (outerUInterval C i) *
          productEnvelope C (outerXInterval C i)).upperRat : ℝ) := by
    apply mul_le_intervalUpper (norm_nonneg _) hp0
    · exact hk
    · exact hpCell.trans hpUpper
  have hjacContains :
      (div (rat 1) (rat (2 * C.hi))).Contains
        (1 / (2 * (C.hi : ℝ))) :=
    contains_div htwoExact
      (by simpa using contains_rat (1 : ℚ))
      (by simpa using contains_rat (2 * C.hi))
  have hfinal :=
    mul_le_intervalUpper
      (mul_nonneg (norm_nonneg _) hp0)
      (by positivity : 0 ≤ (1 / (2 * (C.hi : ℝ))))
      hkp (le_upperRat hjacContains)
  unfold outerScaledIntegrand
  simpa [div_eq_mul_inv, mul_assoc] using hfinal

private theorem foldl_range_add_eq_finsetSum
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append,
        Finset.sum_range_succ, ih]
      simp

/--
The reflected core rectangle sum bounds the actual core integral when every
noninitial core node satisfies its local executable safety check.
-/
theorem coreIntegral_le_of_safe
    {C : Cell} {L : ℝ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hsafeCore : ∀ i < C.coreCells,
      (if i = 0 then true else coreIntegrandSafe C i) = true) :
    (∫ u : ℝ in 0..(C.cutoff : ℝ),
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
      (coreIntegralUpper C : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, _hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, _hfourL,
      hcore, _houter, _hband⟩
  have hLpos : 0 < L := by
    have : (0 : ℝ) < C.lo := by exact_mod_cast hlo
    exact this.trans_le hL
  have hcutoffReal : (0 : ℝ) < C.cutoff := by
    exact_mod_cast hcutoff
  have hbandReal : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hcutReal : (C.cutoff : ℝ) ≤ C.bandwidth := by
    exact_mod_cast hcut
  have hcoreNat : 0 < C.coreCells := hcore
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)
  have hglobal :
      IntervalIntegrable f volume 0 (C.cutoff : ℝ) := by
    exact intervalIntegrable_tyurinCoreIntegrand
      (n := innerTrapezoids)
      (by norm_num [innerTrapezoids]) hLpos hcutoffReal
      hbandReal hcutReal
  have hsum :=
    intervalIntegral_le_uniformCellSum
      (f := f) (A := 0) (B := (C.cutoff : ℝ))
      (M := fun i => (coreCellUpper C i : ℝ))
      C.coreCells (by exact_mod_cast hcutoff.le)
      hcoreNat
      (by
        intro i hi
        apply IntervalIntegrable.mono_set hglobal
        have hleftEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * i =
              (C.cutoff : ℝ) * i / C.coreCells := by ring
        have hrightEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * (i + 1) =
              (C.cutoff : ℝ) * (i + 1) / C.coreCells := by ring
        rw [uIcc_of_le (by
          have : (0 : ℝ) ≤ C.cutoff / C.coreCells := by positivity
          gcongr
          exact_mod_cast Nat.le_succ i),
          uIcc_of_le hcutoffReal.le]
        rw [hleftEq, hrightEq]
        intro u hu
        constructor
        · have hi0 : (0 : ℝ) ≤ i := by positivity
          have : 0 ≤ (C.cutoff : ℝ) * i / C.coreCells := by
            positivity
          exact this.trans hu.1
        · have hiSucc : (i + 1 : ℝ) ≤ C.coreCells := by
            exact_mod_cast hi
          calc
            u ≤ (C.cutoff : ℝ) * (i + 1) / C.coreCells := hu.2
            _ ≤ C.cutoff := by
              have hn : (0 : ℝ) < C.coreCells := by
                exact_mod_cast hcore
              rw [div_le_iff₀ hn]
              exact mul_le_mul_of_nonneg_left hiSucc
                hcutoffReal.le)
      (by
        intro i hi u hu
        have hleftEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * i =
              (C.cutoff : ℝ) * i / C.coreCells := by ring
        have hrightEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * (i + 1) =
              (C.cutoff : ℝ) * (i + 1) / C.coreCells := by ring
        rw [hleftEq, hrightEq] at hu
        unfold coreCellUpper
        by_cases hiZero : i = 0
        · rw [if_pos hiZero]
          subst i
          apply firstCore_upper hgeometry hL hLb
            (by simpa using hu.1)
          simpa using hu.2
        · rw [if_neg hiZero]
          have hiPos : 0 < i := Nat.pos_of_ne_zero hiZero
          have hs := hsafeCore i hi
          rw [if_neg hiZero] at hs
          apply coreIntegrand_upper_of_pos
            hgeometry hL hLb hiPos hi hu hs)
  unfold coreIntegralUpper
  rw [foldl_range_add_eq_finsetSum]
  simpa [f, sub_zero, mul_div_assoc] using hsum

/--
The granular reflected core rectangle sum bounds the actual core integral
when every noninitial node's stored discrepancy/kernel choice is safe.
-/
theorem chosenCoreIntegral_le_of_safe
    {C : Cell} {L : ℝ} (choices : ℕ → CoreChoice)
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hsafeCore : ∀ i < C.coreCells,
      (if i = 0 then true
        else chosenCoreIntegrandSafe C (choices i) i) = true) :
    (∫ u : ℝ in 0..(C.cutoff : ℝ),
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
      (chosenCoreIntegralUpper C choices : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, _hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, _hfourL,
      hcore, _houter, _hband⟩
  have hLpos : 0 < L := by
    have : (0 : ℝ) < C.lo := by exact_mod_cast hlo
    exact this.trans_le hL
  have hcutoffReal : (0 : ℝ) < C.cutoff := by
    exact_mod_cast hcutoff
  have hbandReal : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hcutReal : (C.cutoff : ℝ) ≤ C.bandwidth := by
    exact_mod_cast hcut
  have hcoreNat : 0 < C.coreCells := hcore
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)
  have hglobal :
      IntervalIntegrable f volume 0 (C.cutoff : ℝ) := by
    exact intervalIntegrable_tyurinCoreIntegrand
      (n := innerTrapezoids)
      (by norm_num [innerTrapezoids]) hLpos hcutoffReal
      hbandReal hcutReal
  have hsum :=
    intervalIntegral_le_uniformCellSum
      (f := f) (A := 0) (B := (C.cutoff : ℝ))
      (M := fun i =>
        (chosenCoreCellUpper C (choices i) i : ℝ))
      C.coreCells (by exact_mod_cast hcutoff.le)
      hcoreNat
      (by
        intro i hi
        apply IntervalIntegrable.mono_set hglobal
        have hleftEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * i =
              (C.cutoff : ℝ) * i / C.coreCells := by ring
        have hrightEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * (i + 1) =
              (C.cutoff : ℝ) * (i + 1) / C.coreCells := by ring
        rw [uIcc_of_le (by
          have : (0 : ℝ) ≤ C.cutoff / C.coreCells := by positivity
          gcongr
          exact_mod_cast Nat.le_succ i),
          uIcc_of_le hcutoffReal.le]
        rw [hleftEq, hrightEq]
        intro u hu
        constructor
        · have : 0 ≤ (C.cutoff : ℝ) * i / C.coreCells := by
            positivity
          exact this.trans hu.1
        · have hiSucc : (i + 1 : ℝ) ≤ C.coreCells := by
            exact_mod_cast hi
          calc
            u ≤ (C.cutoff : ℝ) * (i + 1) / C.coreCells := hu.2
            _ ≤ C.cutoff := by
              have hn : (0 : ℝ) < C.coreCells := by
                exact_mod_cast hcore
              rw [div_le_iff₀ hn]
              exact mul_le_mul_of_nonneg_left hiSucc
                hcutoffReal.le)
      (by
        intro i hi u hu
        have hleftEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * i =
              (C.cutoff : ℝ) * i / C.coreCells := by ring
        have hrightEq :
            0 + ((C.cutoff : ℝ) - 0) / C.coreCells * (i + 1) =
              (C.cutoff : ℝ) * (i + 1) / C.coreCells := by ring
        rw [hleftEq, hrightEq] at hu
        unfold chosenCoreCellUpper
        by_cases hiZero : i = 0
        · rw [if_pos hiZero]
          subst i
          apply firstCore_upper hgeometry hL hLb
            (by simpa using hu.1)
          simpa using hu.2
        · rw [if_neg hiZero]
          have hiPos : 0 < i := Nat.pos_of_ne_zero hiZero
          have hs := hsafeCore i hi
          rw [if_neg hiZero] at hs
          apply chosenCoreIntegrand_upper_of_pos
            (choices i) hgeometry hL hLb hiPos hi hu hs)
  unfold chosenCoreIntegralUpper
  rw [foldl_range_add_eq_finsetSum]
  simpa [f, sub_zero, mul_div_assoc] using hsum

/-- The complete reflected safety check supplies every core-node premise. -/
theorem coreIntegral_le
    {C : Cell} {L : ℝ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hsafe : numericSafeCheck C = true) :
    (∫ u : ℝ in 0..(C.cutoff : ℝ),
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
      (coreIntegralUpper C : ℝ) := by
  unfold numericSafeCheck at hsafe
  rw [Bool.and_eq_true] at hsafe
  have hsafeCore := hsafe.1
  rw [List.all_eq_true] at hsafeCore
  apply coreIntegral_le_of_safe hgeometry hL hLb
  intro i hi
  exact hsafeCore i (by simpa using hi)

/--
The reflected scaled-outer rectangle sum bounds the actual outer integral
when every outer node satisfies its local executable safety check.
-/
theorem outerIntegral_le_of_safe
    {C : Cell} {L : ℝ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hsafeOuter : ∀ i < C.outerCells,
      outerScaledIntegrandSafe C i = true) :
    (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ),
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        tyurinProductEnvelope L u) ≤
      (outerIntegralUpper C : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, _hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, _hfourL,
      _hcore, houter, hbandGeom⟩
  have hLpos : 0 < L := by
    have : (0 : ℝ) < C.lo := by exact_mod_cast hlo
    exact this.trans_le hL
  have hcutoffReal : (0 : ℝ) < C.cutoff := by
    exact_mod_cast hcutoff
  have hbandReal : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hcutReal : (C.cutoff : ℝ) ≤ C.bandwidth := by
    exact_mod_cast hcut
  have hb : (0 : ℝ) < C.hi := hLpos.trans_le hLb
  have houterNat : 0 < C.outerCells := houter
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
      tyurinProductEnvelope L u
  have hglobal :
      IntervalIntegrable f volume
        (C.cutoff : ℝ) (C.bandwidth : ℝ) :=
    intervalIntegrable_tyurinOuterIntegrand
      hLpos hcutoffReal hbandReal hcutReal
  have hsum :=
    intervalIntegral_le_uniformCellSum
      (f := f) (A := (C.cutoff : ℝ))
      (B := (C.bandwidth : ℝ))
      (M := fun i => (2 * (C.hi : ℝ)) *
        (outerCellUpper C i : ℝ))
      C.outerCells hcutReal houterNat
      (by
        intro i hi
        apply IntervalIntegrable.mono_set hglobal
        have hn : (0 : ℝ) < C.outerCells := by
          exact_mod_cast houter
        have hi0 : (0 : ℝ) ≤ i := by positivity
        have hiSucc : (i + 1 : ℝ) ≤ C.outerCells := by
          exact_mod_cast hi
        have hcellOrder :
            (C.cutoff : ℝ) +
                ((C.bandwidth : ℝ) - C.cutoff) /
                  C.outerCells * i ≤
              C.cutoff +
                (C.bandwidth - C.cutoff) /
                  C.outerCells * (i + 1) := by
          have hwidth :
              0 ≤ ((C.bandwidth : ℝ) - C.cutoff) /
                C.outerCells := by positivity
          nlinarith
        rw [uIcc_of_le hcellOrder, uIcc_of_le hcutReal]
        intro u hu
        constructor
        · have hstep :
              0 ≤ ((C.bandwidth : ℝ) - C.cutoff) /
                C.outerCells * i := by positivity
          linarith [hu.1]
        · have hstep :
              ((C.bandwidth : ℝ) - C.cutoff) /
                    C.outerCells * (i + 1) ≤
                  C.bandwidth - C.cutoff := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hn]
            exact mul_le_mul_of_nonneg_left hiSucc
              (sub_nonneg.mpr hcutReal)
          linarith [hu.2])
      (by
        intro i hi u hu
        have hn : (0 : ℝ) < C.outerCells := by
          exact_mod_cast houter
        have hleftEq :
            (C.cutoff : ℝ) +
                ((C.bandwidth : ℝ) - C.cutoff) /
                  C.outerCells * i =
              C.cutoff +
                (C.bandwidth - C.cutoff) * i /
                  C.outerCells := by ring
        have hrightEq :
            (C.cutoff : ℝ) +
                ((C.bandwidth : ℝ) - C.cutoff) /
                  C.outerCells * (i + 1) =
              C.cutoff +
                (C.bandwidth - C.cutoff) * (i + 1) /
                  C.outerCells := by ring
        rw [hleftEq, hrightEq] at hu
        have hx :
            (outerXInterval C i).Contains
              (2 * (C.hi : ℝ) * u) := by
          unfold outerXInterval
          dsimp only
          apply Interval.contains_enclose
          have hleftX :
              ((2 * C.hi * C.cutoff : ℚ) +
                  (2 * C.hi * C.bandwidth -
                    2 * C.hi * C.cutoff) * i /
                    C.outerCells : ℚ) =
                2 * C.hi *
                  (C.cutoff +
                    (C.bandwidth - C.cutoff) * i /
                      C.outerCells) := by ring
          have hrightX :
              ((2 * C.hi * C.cutoff : ℚ) +
                  (2 * C.hi * C.bandwidth -
                    2 * C.hi * C.cutoff) * (i + 1) /
                    C.outerCells : ℚ) =
                2 * C.hi *
                  (C.cutoff +
                    (C.bandwidth - C.cutoff) * (i + 1) /
                      C.outerCells) := by ring
          rw [hleftX, hrightX]
          push_cast
          constructor
          · exact mul_le_mul_of_nonneg_left hu.1
              (by positivity : 0 ≤ 2 * (C.hi : ℝ))
          · exact mul_le_mul_of_nonneg_left hu.2
              (by positivity : 0 ≤ 2 * (C.hi : ℝ))
        have huCut : (C.cutoff : ℝ) ≤ u := by
          have hnonneg :
              0 ≤ ((C.bandwidth : ℝ) - C.cutoff) * i /
                C.outerCells := by positivity
          linarith [hu.1]
        have huU : u ≤ (C.bandwidth : ℝ) := by
          have hiSucc : (i + 1 : ℝ) ≤ C.outerCells := by
            exact_mod_cast hi
          calc
            u ≤ C.cutoff +
                (C.bandwidth - C.cutoff) * (i + 1) /
                  C.outerCells := hu.2
            _ ≤ C.bandwidth := by
              have hfrac :
                  ((C.bandwidth : ℝ) - C.cutoff) *
                        (i + 1) / C.outerCells ≤
                    C.bandwidth - C.cutoff := by
                rw [div_le_iff₀ hn]
                exact mul_le_mul_of_nonneg_left hiSucc
                  (sub_nonneg.mpr hcutReal)
              linarith
        have hband :
            2 * (C.hi : ℝ) * u ≤ 157 / 25 := by
          have hgeomReal :
              2 * (C.hi : ℝ) * C.bandwidth ≤
                (157 / 25 : ℝ) := by
            have hcast := (Rat.cast_le (K := ℝ)).2 hbandGeom
            norm_num at hcast ⊢
            exact hcast
          nlinarith
        have hs := hsafeOuter i hi
        have hscaled :=
          outerScaledIntegrand_upper hgeometry hL hLb
            huCut huU hx hband hs
        have hden : 0 < 2 * (C.hi : ℝ) := by positivity
        have hrecover :
            f u ≤ (outerCellUpper C i : ℝ) *
                (2 * (C.hi : ℝ)) := by
          apply (div_le_iff₀ hden).mp
          simpa [f, outerCellUpper] using hscaled
        simpa [mul_comm] using hrecover)
  have hsumFactor :
      (∑ i ∈ Finset.range C.outerCells,
          2 * (C.hi : ℝ) * (outerCellUpper C i : ℝ)) =
        2 * (C.hi : ℝ) *
          ∑ i ∈ Finset.range C.outerCells,
            (outerCellUpper C i : ℝ) := by
    rw [Finset.mul_sum]
  rw [hsumFactor] at hsum
  calc
    _ ≤
        ((C.bandwidth : ℝ) - C.cutoff) / C.outerCells *
          (2 * (C.hi : ℝ) *
            ∑ i ∈ Finset.range C.outerCells,
              (outerCellUpper C i : ℝ)) := by simpa [f] using hsum
    _ = (outerIntegralUpper C : ℝ) := by
      unfold outerIntegralUpper
      dsimp only
      rw [foldl_range_add_eq_finsetSum]
      push_cast
      ring

/-- The complete reflected safety check supplies every outer-node premise. -/
theorem outerIntegral_le
    {C : Cell} {L : ℝ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hsafe : numericSafeCheck C = true) :
    (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ),
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        tyurinProductEnvelope L u) ≤
      (outerIntegralUpper C : ℝ) := by
  unfold numericSafeCheck at hsafe
  rw [Bool.and_eq_true] at hsafe
  have hsafeOuter := hsafe.2
  rw [List.all_eq_true] at hsafeOuter
  apply outerIntegral_le_of_safe hgeometry hL hLb
  intro i hi
  exact hsafeOuter i (by simpa using hi)

/-- The reflected negative-exponential endpoint bounds the exact Gaussian tail. -/
theorem gaussianExpUpper_sound (C : Cell) :
    Real.exp (-((C.cutoff : ℝ) ^ 2) / 2) ≤
      (gaussianExpUpper C : ℝ) := by
  have hcontains :=
    Exp.negUpper_contains
      (p := precision) (k := squarings)
      (x := C.cutoff ^ 2 / 2) (by positivity)
  unfold gaussianExpUpper
  calc
    Real.exp (-((C.cutoff : ℝ) ^ 2) / 2) =
        Real.exp (-((C.cutoff ^ 2 / 2 : ℚ) : ℝ)) := by
          congr 1
          norm_num
          ring
    _ ≤ ((Exp.negUpper precision
          (C.cutoff ^ 2 / 2) squarings).upperRat : ℝ) := by
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using
        hcontains.2

/--
The sharp Gaussian correction and tail budget is bounded by the tight
six-decimal rational budget evaluated by the cell checker.
-/
theorem gaussianSharpClosedBudget_le
    {C : Cell}
    (hgeometry : geometryCheck C = true) :
    prawitzGaussianSharpClosedBudget
        (C.cutoff : ℝ) (C.bandwidth : ℝ) ≤
      (gaussianBudgetUpper C : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, _hfourL,
      _hcore, _houter, _hband⟩
  have hU₀ : (0 : ℝ) < C.cutoff := by exact_mod_cast hcutoff
  have hU : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  let e : ℝ := (gaussianExpUpper C : ℝ)
  have hexp :
      Real.exp (-((C.cutoff : ℝ) ^ 2) / 2) ≤ e :=
    gaussianExpUpper_sound C
  have he0 : 0 ≤ e :=
    (Real.exp_nonneg _).trans hexp
  have hsqrt :
      Real.sqrt (2 * Real.pi) ≤
        (sqrtTwoPiUpper : ℝ) := by
    simpa [sqrtTwoPiUpper] using
      sqrt_two_pi_lt_250663_div_100000.le
  have hpi :
      Real.pi ≤ (piUpper : ℝ) := by
    simpa [piUpper] using pi_lt_3141593_div_1000000.le
  have hpiSq :
      Real.pi ^ 2 ≤ (piUpper : ℝ) ^ 2 :=
    (sq_le_sq₀ Real.pi_pos.le
      (by norm_num [piUpper])).2 hpi
  have hprod :
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) ≤
        (piUpper : ℝ) ^ 2 *
          (sqrtTwoPiUpper : ℝ) :=
    mul_le_mul hpiSq hsqrt (Real.sqrt_nonneg _)
      (sq_nonneg _)
  have hinvPi :
      1 / Real.pi ≤ 1 / (piLower : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    have hpilo :
        (piLower : ℝ) < Real.pi := by
      simpa [piLower] using pi_gt_3141592_div_1000000
    have hpositive : (0 : ℝ) ≤ 1 / (piLower : ℝ) := by
      norm_num [piLower]
    calc
      (1 : ℝ) =
          (1 / (piLower : ℝ)) *
            (piLower : ℝ) := by
              norm_num [piLower]
      _ ≤ (1 / (piLower : ℝ)) * Real.pi :=
        mul_le_mul_of_nonneg_left hpilo.le hpositive
  have htailNumerator :
      Real.exp (-((C.cutoff : ℝ) ^ 2) / 2) *
          (1 / Real.pi) ≤
        e * (1 / (piLower : ℝ)) :=
    mul_le_mul hexp hinvPi (by positivity) he0
  unfold prawitzGaussianSharpClosedBudget
    prawitzGaussianSharpCoreBudget
  have hfirst :
      Real.sqrt (2 * Real.pi) /
          (2 * (C.bandwidth : ℝ)) ≤
        (sqrtTwoPiUpper : ℝ) /
          (2 * (C.bandwidth : ℝ)) :=
    div_le_div_of_nonneg_right hsqrt (by positivity)
  have hnegative :
      -(1 - Real.exp (-((C.cutoff : ℝ) ^ 2) / 2)) /
            (C.bandwidth : ℝ) ^ 2 ≤
        -(1 - e) / (C.bandwidth : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right (by linarith)
      (sq_nonneg (C.bandwidth : ℝ))
  have hthird :
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) /
            (36 * (C.bandwidth : ℝ) ^ 3) ≤
        (piUpper : ℝ) ^ 2 *
            (sqrtTwoPiUpper : ℝ) /
              (36 * (C.bandwidth : ℝ) ^ 3) :=
    div_le_div_of_nonneg_right hprod (by positivity)
  have htail :
      Real.exp (-((C.cutoff : ℝ) ^ 2) / 2) /
            (Real.pi * (C.cutoff : ℝ) ^ 2) ≤
        (1 / (piLower : ℝ)) * e /
            (C.cutoff : ℝ) ^ 2 := by
    calc
      Real.exp (-((C.cutoff : ℝ) ^ 2) / 2) /
            (Real.pi * (C.cutoff : ℝ) ^ 2) =
          (Real.exp (-((C.cutoff : ℝ) ^ 2) / 2) *
            (1 / Real.pi)) / (C.cutoff : ℝ) ^ 2 := by
              field_simp [Real.pi_ne_zero, hU₀.ne']
      _ ≤ (e * (1 / (piLower : ℝ))) /
            (C.cutoff : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right htailNumerator
          (sq_nonneg (C.cutoff : ℝ))
      _ = (1 / (piLower : ℝ)) * e /
            (C.cutoff : ℝ) ^ 2 := by ring
  have hsum :=
    add_le_add
      (add_le_add (add_le_add hfirst hnegative) hthird)
      htail
  unfold gaussianBudgetUpper
  dsimp only
  change _ ≤
    ((sqrtTwoPiUpper / (2 * C.bandwidth) -
      (1 - gaussianExpUpper C) / C.bandwidth ^ 2 +
      piUpper ^ 2 * sqrtTwoPiUpper /
        (36 * C.bandwidth ^ 3) +
      (1 / piLower) * gaussianExpUpper C /
        C.cutoff ^ 2 : ℚ) : ℝ)
  push_cast
  simpa only [e, sub_eq_add_neg, neg_div] using hsum

/--
One successful reflected cell check proves the strict `3 / 5` D-star bound
throughout that cell's closed Lyapunov interval.
-/
theorem tyurinRationalDStar_lt_three_fifths_of_cell
    {C : Cell} {L : ℝ}
    (hcheck : cellCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ)) :
    tyurinRationalDStar L
        (C.cutoff : ℝ) (C.bandwidth : ℝ) < 3 / 5 := by
  unfold cellCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hchecks, hstrict⟩
  rw [Bool.and_eq_true] at hchecks
  rcases hchecks with ⟨hgeometry, hsafe⟩
  have hstrictRat :
      numeratorUpper C < cellTarget C :=
    of_decide_eq_true hstrict
  have hLpos : 0 < L := by
    have hlo : (0 : ℝ) < C.lo := by
      exact_mod_cast (geometryCheck_sound hgeometry).1
    exact hlo.trans_le hL
  have hcore :=
    coreIntegral_le hgeometry hL hLb hsafe
  have houter :=
    outerIntegral_le hgeometry hL hLb hsafe
  have hgaussian :=
    gaussianSharpClosedBudget_le hgeometry
  have hnumerator :
      2 * (∫ u : ℝ in 0..(C.cutoff : ℝ),
          ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
            min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) +
        2 * (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ),
          ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
            tyurinProductEnvelope L u) +
        prawitzGaussianSharpClosedBudget
          (C.cutoff : ℝ) (C.bandwidth : ℝ) ≤
        (numeratorUpper C : ℝ) := by
    unfold numeratorUpper
    push_cast
    nlinarith
  have htarget :
      (numeratorUpper C : ℝ) < (3 / 5 : ℝ) * L := by
    calc
      (numeratorUpper C : ℝ) <
          (cellTarget C : ℝ) :=
        (Rat.cast_lt (K := ℝ)).2 hstrictRat
      _ = (3 / 5 : ℝ) * (C.lo : ℝ) := by
        unfold cellTarget
        push_cast
        rfl
      _ ≤ (3 / 5 : ℝ) * L := by gcongr
  unfold tyurinRationalDStar
  rw [div_lt_iff₀ hLpos]
  nlinarith

/--
Granular certificate interface for large cells.  It avoids unfolding one
monolithic Boolean: callers may prove local safety and the three rational
budget bounds in independently cached chunks.
-/
theorem tyurinRationalDStar_lt_three_fifths_of_reflectedBounds
    {C : Cell} {L : ℝ} {coreBound outerBound gaussianBound : ℚ}
    (hgeometry : geometryCheck C = true)
    (hsafeCore : ∀ i < C.coreCells,
      (if i = 0 then true else coreIntegrandSafe C i) = true)
    (hsafeOuter : ∀ i < C.outerCells,
      outerScaledIntegrandSafe C i = true)
    (hcoreEval : coreIntegralUpper C ≤ coreBound)
    (houterEval : outerIntegralUpper C ≤ outerBound)
    (hgaussianEval : gaussianBudgetUpper C ≤ gaussianBound)
    (hfinal :
      2 * coreBound + 2 * outerBound + gaussianBound <
        cellTarget C)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ)) :
    tyurinRationalDStar L
        (C.cutoff : ℝ) (C.bandwidth : ℝ) < 3 / 5 := by
  have hLpos : 0 < L := by
    have hlo : (0 : ℝ) < C.lo := by
      exact_mod_cast (geometryCheck_sound hgeometry).1
    exact hlo.trans_le hL
  have hcoreActual :=
    coreIntegral_le_of_safe hgeometry hL hLb hsafeCore
  have houterActual :=
    outerIntegral_le_of_safe hgeometry hL hLb hsafeOuter
  have hgaussianActual :=
    gaussianSharpClosedBudget_le hgeometry
  have hcoreCast :
      (coreIntegralUpper C : ℝ) ≤ (coreBound : ℝ) :=
    (Rat.cast_le (K := ℝ)).2 hcoreEval
  have houterCast :
      (outerIntegralUpper C : ℝ) ≤ (outerBound : ℝ) :=
    (Rat.cast_le (K := ℝ)).2 houterEval
  have hgaussianCast :
      (gaussianBudgetUpper C : ℝ) ≤ (gaussianBound : ℝ) :=
    (Rat.cast_le (K := ℝ)).2 hgaussianEval
  have hnumerator :
      2 * (∫ u : ℝ in 0..(C.cutoff : ℝ),
          ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
            min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) +
        2 * (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ),
          ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
            tyurinProductEnvelope L u) +
        prawitzGaussianSharpClosedBudget
          (C.cutoff : ℝ) (C.bandwidth : ℝ) ≤
        2 * (coreBound : ℝ) + 2 * (outerBound : ℝ) +
          (gaussianBound : ℝ) := by
    nlinarith
  have hfinalCast :
      2 * (coreBound : ℝ) + 2 * (outerBound : ℝ) +
          (gaussianBound : ℝ) <
        (cellTarget C : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 hfinal
    norm_num at this ⊢
    exact this
  have htarget :
      (cellTarget C : ℝ) ≤ (3 / 5 : ℝ) * L := by
    unfold cellTarget
    push_cast
    gcongr
  unfold tyurinRationalDStar
  rw [div_lt_iff₀ hLpos]
  nlinarith

/--
Granular certificate interface with one stored discrepancy/kernel choice at
each core node.  Only the selected alternatives are evaluated.
-/
theorem tyurinRationalDStar_lt_three_fifths_of_chosenReflectedBounds
    {C : Cell} {L : ℝ} (choices : ℕ → CoreChoice)
    {coreBound outerBound gaussianBound : ℚ}
    (hgeometry : geometryCheck C = true)
    (hsafeCore : ∀ i < C.coreCells,
      (if i = 0 then true
        else chosenCoreIntegrandSafe C (choices i) i) = true)
    (hsafeOuter : ∀ i < C.outerCells,
      outerScaledIntegrandSafe C i = true)
    (hcoreEval : chosenCoreIntegralUpper C choices ≤ coreBound)
    (houterEval : outerIntegralUpper C ≤ outerBound)
    (hgaussianEval : gaussianBudgetUpper C ≤ gaussianBound)
    (hfinal :
      2 * coreBound + 2 * outerBound + gaussianBound <
        cellTarget C)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ)) :
    tyurinRationalDStar L
        (C.cutoff : ℝ) (C.bandwidth : ℝ) < 3 / 5 := by
  have hLpos : 0 < L := by
    have hlo : (0 : ℝ) < C.lo := by
      exact_mod_cast (geometryCheck_sound hgeometry).1
    exact hlo.trans_le hL
  have hcoreActual :=
    chosenCoreIntegral_le_of_safe choices hgeometry hL hLb hsafeCore
  have houterActual :=
    outerIntegral_le_of_safe hgeometry hL hLb hsafeOuter
  have hgaussianActual :=
    gaussianSharpClosedBudget_le hgeometry
  have hcoreCast :
      (chosenCoreIntegralUpper C choices : ℝ) ≤
        (coreBound : ℝ) :=
    (Rat.cast_le (K := ℝ)).2 hcoreEval
  have houterCast :
      (outerIntegralUpper C : ℝ) ≤ (outerBound : ℝ) :=
    (Rat.cast_le (K := ℝ)).2 houterEval
  have hgaussianCast :
      (gaussianBudgetUpper C : ℝ) ≤ (gaussianBound : ℝ) :=
    (Rat.cast_le (K := ℝ)).2 hgaussianEval
  have hnumerator :
      2 * (∫ u : ℝ in 0..(C.cutoff : ℝ),
          ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
            min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) +
        2 * (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ),
          ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
            tyurinProductEnvelope L u) +
        prawitzGaussianSharpClosedBudget
          (C.cutoff : ℝ) (C.bandwidth : ℝ) ≤
        2 * (coreBound : ℝ) + 2 * (outerBound : ℝ) +
          (gaussianBound : ℝ) := by
    nlinarith
  have hfinalCast :
      2 * (coreBound : ℝ) + 2 * (outerBound : ℝ) +
          (gaussianBound : ℝ) <
        (cellTarget C : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 hfinal
    norm_num at this ⊢
    exact this
  have htarget :
      (cellTarget C : ℝ) ≤ (3 / 5 : ℝ) * L := by
    unfold cellTarget
    push_cast
    gcongr
  unfold tyurinRationalDStar
  rw [div_lt_iff₀ hLpos]
  nlinarith

end TyurinModerate
end CertifiedJL
