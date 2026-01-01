/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.HistoryThenFresh
import CertifiedJL.Protocol.Acceptance
import CertifiedJL.Statements.Transport.Upper

/-!
# Affine tail bounds after a prior history

These adapters apply pointwise shifted tail bounds when a prior history
selects the dimension, modulus, witness, public threshold, and row-wise shift
before the matrix is sampled from the prescribed distribution. They do not
formalize a prover, verifier, transcript semantics, or zero knowledge. A
protocol application must prove that its experiment is the displayed two-stage
`historyThenFreshMatrix` PMF.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL

universe u v

/-- A uniform affine L2 upper tail remains valid when the input, modulus, and
fixed shift are selected from a prior history before the fresh matrix. -/
theorem AffineL2UpperTailAt.history_le
    {parameters : L2UpperParameters} {budget : ENNReal}
    (htail : AffineL2UpperTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x => AffineL2UpperFailureWithShift parameters.threshold
        (modulus x.1) (shift x.1) (witness x.1) x.2) ≤ budget := by
  apply eventProbability_historyThenFreshMatrix_le parameters.rows dimension
    history (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
    (fun h J => AffineL2UpperFailureWithShift parameters.threshold
      (modulus h) (shift h) (witness h) J) budget
  intro h
  exact (htail (modulus h) (dimension h) (witness h) (shift h)).le

/-- A uniform affine L-infinity upper tail remains valid when the input,
modulus, and fixed shift are selected from a prior history. -/
theorem AffineLInfUpperTailAt.history_le
    {parameters : LInfUpperParameters} {budget : ENNReal}
    (htail : AffineLInfUpperTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x => AffineLInfUpperFailureWithShift parameters
        (modulus x.1) (shift x.1) (witness x.1) x.2) ≤ budget := by
  apply eventProbability_historyThenFreshMatrix_le parameters.rows dimension
    history (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
    (fun h J => AffineLInfUpperFailureWithShift parameters
      (modulus h) (shift h) (witness h) J) budget
  intro h
  exact (htail (modulus h) (dimension h) (witness h) (shift h)).le
/-- Validity hypotheses required before applying an affine L-infinity lower
tail to a history-selected witness.  The bad-witness norm condition is kept
separate so it can remain inside the joint event. -/
def AffineLInfHistoryValid
    (parameters : LInfThresholdLowerParameters)
    {History : Type u} (dimension modulus inputThreshold : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ) : History → Prop :=
  fun h => Odd (modulus h) ∧ CenteredInput (modulus h) (witness h) ∧
    0 < inputThreshold h ∧
    InputThresholdWithinModulus parameters.modulusMargin (modulus h)
      (inputThreshold h)

/-- The norm condition defining a bad witness. -/
def AffineHistoryBadWitness
    {History : Type u} (dimension inputThreshold : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ) : History → Prop :=
  fun h => InputThresholdAtMostNorm (inputThreshold h) (witness h)

/-- L2 validity hypotheses required before applying an affine lower tail to
a history-selected witness.  As in the L-infinity lane, the norm condition is
kept out of validity and inside the joint bad-witness event. -/
def AffineL2HistoryValid
    (parameters : L2ThresholdLowerParameters)
    {History : Type u} (dimension modulus inputThreshold : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ) : History → Prop :=
  fun h => Odd (modulus h) ∧ CenteredInput (modulus h) (witness h) ∧
    0 < inputThreshold h ∧
    InputThresholdWithinModulus parameters.modulusMargin (modulus h)
      (inputThreshold h)

/-- L2 sibling of `AffineLInfThresholdLowerTailAt.history_joint_le`. -/
theorem AffineL2ThresholdLowerTailAt.history_joint_le
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    (htail : AffineL2ThresholdLowerTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus inputThreshold : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x =>
        AffineL2HistoryValid parameters dimension modulus inputThreshold
            witness x.1 ∧
          AffineHistoryBadWitness dimension inputThreshold witness x.1 ∧
          AffineL2ThresholdLowerFailure parameters.squaredNormFloor
            (inputThreshold x.1) (modulus x.1) (shift x.1)
            (witness x.1) x.2) ≤ budget := by
  refine eventProbability_historyThenFreshMatrix_le parameters.rows dimension
    history (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
    (fun h J =>
      AffineL2HistoryValid parameters dimension modulus inputThreshold
          witness h ∧
        AffineHistoryBadWitness dimension inputThreshold witness h ∧
        AffineL2ThresholdLowerFailure parameters.squaredNormFloor (inputThreshold h)
          (modulus h) (shift h) (witness h) J) budget ?_
  intro h
  by_cases hv : AffineL2HistoryValid parameters dimension modulus
      inputThreshold witness h
  · by_cases hb : AffineHistoryBadWitness dimension inputThreshold witness h
    · simpa [hv, hb] using
        (htail (modulus h) (dimension h) (witness h) (inputThreshold h)
          (shift h) hv.1 hv.2.1 hv.2.2.1 hb hv.2.2.2).le
    · simpa [hv, hb]
  · simpa [hv]

/-- Uniform affine lower tails bound the joint event in which the history is
valid, its selected witness is bad, and the independently sampled matrix
accepts it. -/
theorem AffineLInfThresholdLowerTailAt.history_joint_le
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    (htail : AffineLInfThresholdLowerTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus inputThreshold : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x =>
        AffineLInfHistoryValid parameters dimension modulus inputThreshold
            witness x.1 ∧
          AffineHistoryBadWitness dimension inputThreshold witness x.1 ∧
          AffineLInfThresholdSmallProjection parameters (inputThreshold x.1)
            (modulus x.1) (shift x.1) (witness x.1) x.2) ≤ budget := by
  refine eventProbability_historyThenFreshMatrix_le parameters.rows dimension
    history (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
    (fun h J =>
      AffineLInfHistoryValid parameters dimension modulus inputThreshold
          witness h ∧
        AffineHistoryBadWitness dimension inputThreshold witness h ∧
        AffineLInfThresholdSmallProjection parameters (inputThreshold h)
          (modulus h) (shift h) (witness h) J) budget ?_
  intro h
  by_cases hv : AffineLInfHistoryValid parameters dimension modulus
      inputThreshold witness h
  · by_cases hb : AffineHistoryBadWitness dimension inputThreshold witness h
    · simpa [hv, hb] using
        (htail (modulus h) (dimension h) (witness h) (inputThreshold h)
          (shift h) hv.1 hv.2.1 hv.2.2.1 hb hv.2.2.2).le
    · simpa [hv, hb]
  · simpa [hv]
/-- L2 invalid-history adapter with the bad-witness norm condition retained
inside the joint event. -/
theorem AffineL2ThresholdLowerTailAt.history_badWitness_le_add_invalid
    {parameters : L2ThresholdLowerParameters} {budget invalidBudget : ENNReal}
    (htail : AffineL2ThresholdLowerTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus inputThreshold : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ)
    (hinvalid : eventProbability history
      (fun h => ¬ AffineL2HistoryValid parameters dimension modulus
        inputThreshold witness h) ≤ invalidBudget) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x =>
        AffineHistoryBadWitness dimension inputThreshold witness x.1 ∧
          AffineL2ThresholdLowerFailure parameters.squaredNormFloor
            (inputThreshold x.1) (modulus x.1) (shift x.1)
            (witness x.1) x.2) ≤ budget + invalidBudget := by
  apply eventProbability_history_bad_le_add_invalid parameters.rows dimension
    history (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
    (AffineL2HistoryValid parameters dimension modulus inputThreshold witness)
    (AffineHistoryBadWitness dimension inputThreshold witness)
    (fun h J => AffineL2ThresholdLowerFailure parameters.squaredNormFloor
      (inputThreshold h) (modulus h) (shift h) (witness h) J)
    budget invalidBudget
  · exact htail.history_joint_le history dimension modulus inputThreshold
      witness shift
  · exact hinvalid

/-- Consumer-facing L2 history adapter combining a history-dependent closed
acceptance radius with separately budgeted invalid histories.  The strict
pointwise fit preserves the strict lower-failure boundary. -/
theorem AffineL2ThresholdLowerTailAt.history_closedAcceptance_le_add_invalid
    {parameters : L2ThresholdLowerParameters} {budget invalidBudget : ENNReal}
    (htail : AffineL2ThresholdLowerTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus inputThreshold : History → ℕ)
    (acceptanceRadius : History → ℝ)
    (hfit : ∀ h, parameters.squaredNormFloor.denominator * acceptanceRadius h ^ 2 <
      parameters.squaredNormFloor.numerator * (inputThreshold h : ℝ) ^ 2)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ)
    (hinvalid : eventProbability history
      (fun h => ¬ AffineL2HistoryValid parameters dimension modulus
        inputThreshold witness h) ≤ invalidBudget) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x =>
        AffineHistoryBadWitness dimension inputThreshold witness x.1 ∧
          AffineL2ClosedAcceptance (acceptanceRadius x.1) (modulus x.1)
            (shift x.1) (witness x.1) x.2) ≤ budget + invalidBudget := by
  letI : MeasurableSpace (FreshMatrixOutcome History parameters.rows dimension) := ⊤
  letI : MeasurableSingletonClass
      (FreshMatrixOutcome History parameters.rows dimension) :=
    ⟨fun _ => MeasurableSet.of_discrete⟩
  let joint := historyThenFreshMatrix parameters.rows dimension history
    (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
  have hlower := htail.history_badWitness_le_add_invalid history dimension
    modulus inputThreshold witness shift hinvalid
  apply (eventProbability_mono joint ?_).trans hlower
  intro x hx
  refine ⟨hx.1, ?_⟩
  exact affineL2ClosedAcceptance_implies_lowerFailure parameters.squaredNormFloor
    (acceptanceRadius x.1) (inputThreshold x.1) (modulus x.1)
    (shift x.1) (witness x.1) x.2 (hfit x.1) hx.2

/-- If invalid histories have probability at most `invalidBudget`, then the
joint bad-witness/acceptance event costs at most the certified tail budget
plus that separately accounted term. -/
theorem AffineLInfThresholdLowerTailAt.history_badWitness_le_add_invalid
    {parameters : LInfThresholdLowerParameters} {budget invalidBudget : ENNReal}
    (htail : AffineLInfThresholdLowerTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus inputThreshold : History → ℕ)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ)
    (hinvalid : eventProbability history
      (fun h => ¬ AffineLInfHistoryValid parameters dimension modulus
        inputThreshold witness h) ≤ invalidBudget) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x =>
        AffineHistoryBadWitness dimension inputThreshold witness x.1 ∧
          AffineLInfThresholdSmallProjection parameters (inputThreshold x.1)
            (modulus x.1) (shift x.1) (witness x.1) x.2) ≤
      budget + invalidBudget := by
  letI : MeasurableSpace (FreshMatrixOutcome History parameters.rows dimension) := ⊤
  letI : MeasurableSingletonClass
      (FreshMatrixOutcome History parameters.rows dimension) :=
    ⟨fun _ => MeasurableSet.of_discrete⟩
  let joint := historyThenFreshMatrix parameters.rows dimension history
    (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
  calc
    eventProbability joint (fun x =>
        AffineHistoryBadWitness dimension inputThreshold witness x.1 ∧
          AffineLInfThresholdSmallProjection parameters (inputThreshold x.1)
            (modulus x.1) (shift x.1) (witness x.1) x.2) ≤
      eventProbability joint (fun x =>
        AffineLInfHistoryValid parameters dimension modulus inputThreshold
            witness x.1 ∧
          AffineHistoryBadWitness dimension inputThreshold witness x.1 ∧
          AffineLInfThresholdSmallProjection parameters (inputThreshold x.1)
            (modulus x.1) (shift x.1) (witness x.1) x.2) +
      eventProbability joint (fun x =>
        ¬ AffineLInfHistoryValid parameters dimension modulus inputThreshold
          witness x.1) := by
        apply (eventProbability_mono joint ?_).trans
          (eventProbability_or_le joint _ _)
        intro x hx
        by_cases hv : AffineLInfHistoryValid parameters dimension modulus
            inputThreshold witness x.1
        · exact Or.inl ⟨hv, hx⟩
        · exact Or.inr hv
    _ ≤ budget + invalidBudget := by
      apply add_le_add
      · exact htail.history_joint_le history dimension modulus inputThreshold
          witness shift
      · dsimp [joint]
        exact (eventProbability_historyThenFreshMatrix_historyEvent
          parameters.rows dimension history
          (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
          (fun h => ¬ AffineLInfHistoryValid parameters dimension modulus
            inputThreshold witness h)).trans_le hinvalid

/-- Consumer-facing L-infinity history adapter combining closed acceptance,
the `max 1 ceil(A/c)` threshold, and separately budgeted invalid histories. -/
theorem AffineLInfThresholdLowerTailAt.history_closedAcceptance_le_add_invalid
    {parameters : LInfThresholdLowerParameters} {budget invalidBudget : ENNReal}
    (htail : AffineLInfThresholdLowerTailAt parameters budget)
    {History : Type u} [Countable History]
    (history : PMF History) (dimension modulus : History → ℕ)
    (acceptanceRadius : History → ℝ)
    (hRadius : ∀ h, 0 ≤ acceptanceRadius h)
    (hcap : 0 < parameters.coordinateCap.numerator)
    (witness : (h : History) → Fin (dimension h) → ℤ)
    (shift : History → Fin parameters.rows → ℤ)
    (hinvalid : eventProbability history (fun h =>
      ¬ AffineLInfHistoryValid parameters dimension modulus
        (fun h => closedLInfInputThreshold parameters.coordinateCap
          (acceptanceRadius h)) witness h) ≤ invalidBudget) :
    eventProbability
      (historyThenFreshMatrix parameters.rows dimension history
        (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h)))
      (fun x =>
        AffineHistoryBadWitness dimension
            (fun h => closedLInfInputThreshold parameters.coordinateCap
              (acceptanceRadius h)) witness x.1 ∧
          AffineLInfClosedAcceptance (acceptanceRadius x.1) (modulus x.1)
            (shift x.1) (witness x.1) x.2) ≤ budget + invalidBudget := by
  letI : MeasurableSpace (FreshMatrixOutcome History parameters.rows dimension) := ⊤
  letI : MeasurableSingletonClass
      (FreshMatrixOutcome History parameters.rows dimension) :=
    ⟨fun _ => MeasurableSet.of_discrete⟩
  let inputThreshold : History → ℕ := fun h =>
    closedLInfInputThreshold parameters.coordinateCap (acceptanceRadius h)
  let joint := historyThenFreshMatrix parameters.rows dimension history
    (fun h => parameters.distribution.matrixPMF parameters.rows (dimension h))
  have hsmall := htail.history_badWitness_le_add_invalid history dimension
    modulus inputThreshold witness shift (by simpa [inputThreshold] using hinvalid)
  apply (eventProbability_mono joint ?_).trans hsmall
  intro x hx
  refine ⟨hx.1, ?_⟩
  exact affineLInfClosedAcceptance_implies_smallProjection parameters
    (acceptanceRadius x.1) (hRadius x.1) hcap (modulus x.1)
    (shift x.1) (witness x.1) x.2 hx.2

end CertifiedJL
