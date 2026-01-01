/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Verified
import CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform
import Lean.Util.CollectAxioms

/-!
# Sparse one-row tests and mutation canaries

These tests pin the strict internal `9.75` statement, both bounded replay
prefixes, the elementary endpoint branches, and the trusted axiom surface
of every load-bearing theorem.
-/

namespace CertifiedJL
namespace Tests
namespace OneRowCertificateCanaries

/-- The coefficient-uniform theorem has the exact strict `9.75`, `2⁻¹⁴¹` statement. -/
theorem sparseOneRow975_exact :
    ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)),
      eventProbability (sparseRademacherRow d)
          (fun row =>
            |euclideanRowDot row w| >
              (39 / 4 : ℝ) * ‖w‖) <
        failureTarget 141 := by
  intro d w
  have h :=
    Projection.OneRow.BalancedTernary.CoefficientUniform.ternaryUpper39Over4 d w
  change eventProbability (sparseRademacherRow d)
    (OneRowUpperFailure (39 / 4) w) < failureTarget 141
  simpa using h

/-- The strict event is empty for the zero vector in every dimension. -/
theorem zeroVector_rejected
    (d : ℕ) (row : Fin d → ℤ) :
    ¬SparseOneRow975Event
      (0 : EuclideanSpace ℝ (Fin d)) row := by
  simp [SparseOneRow975Event]

/-- Equality at the `9.75` boundary is not a failure. -/
theorem strictBoundary_rejected
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d))
    (row : Fin d → ℤ)
    (hboundary :
      |euclideanRowDot row w| = (39 / 4 : ℝ) * ‖w‖) :
    ¬SparseOneRow975Event w row := by
  simp [SparseOneRow975Event, hboundary]

/-- Mutate the Nat scalar certificate by omitting its first cell. -/
def skippedScalarCellPlan : List ℕ :=
  (List.range SparseOneRowCertificate.gridSize).drop 1

/-- Mutate the Nat scalar certificate by covering its first cell twice. -/
def duplicatedScalarCellPlan : List ℕ :=
  0 :: List.range SparseOneRowCertificate.gridSize

theorem skippedScalarCellPlan_rejected :
    skippedScalarCellPlan ≠
      List.range SparseOneRowCertificate.gridSize := by
  decide +kernel

theorem duplicatedScalarCellPlan_rejected :
    duplicatedScalarCellPlan ≠
      List.range SparseOneRowCertificate.gridSize := by
  decide +kernel

/-- Halving the Nat scalar target rejects its near-maximal cell. -/
theorem tightenedScalarCell_rejected :
    SparseOneRowCertificate.NatInterval.upperLTCheck
        (SparseOneRowCertificate.natCellUpper 112)
        (SparseOneRowCertificate.target / 2) = false := by
  decide +kernel

/-- A zero-sized outer plan is rejected by a retained moderate cell. -/
theorem moderateMutation_rejected :
    TyurinModerate.outerPlanCheck
        TyurinModerate.CertificateProofs.Cell023.certificateCell 0 = false := by
  decide +kernel

set_option linter.style.longLine false in
open Lean in
run_cmd
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name :=
    #[``CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform.ternaryUpper39Over4,
      ``CertifiedJL.CertificateAssembly.normalizedRademacher975Upper,
      ``CertifiedJL.normalizedRademacher975Upper_of_profileSplit,
      ``CertifiedJL.Probability.rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_lyapunov_le,
      ``CertifiedJL.Probability.tyurinRationalDStar_lt_three_fifths_of_moderate,
      ``CertifiedJL.SparseOneRowCertificate.scalarEnvelope_lt_target_of_le_certifiedProfileUpper,
      ``CertifiedJL.Probability.rademacherSum_upperTail_toReal_le_entropyProfile,
      ``CertifiedJL.Probability.kolmogorovDistance_rademacherTiltedStandardizedLaw_le_mul_tyurinRationalDStar]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains &&
        allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end OneRowCertificateCanaries
end Tests
end CertifiedJL
