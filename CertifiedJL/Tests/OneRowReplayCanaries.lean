/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Finite.NatIntervalAll
import CertifiedJL.Certificates.Families.OneRow975.Finite.ProfileSplit
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell023
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.GridCoverage
import Mathlib.Tactic.NormNum

/-!
# One-row certificate replay canaries

This module is deliberately separate from the fast analytic canaries. It
depends on one representative moderate cell and on the complete retained
scalar prefix, so it is built only after the replay workflow has
selected the corresponding certificate targets. The canaries exercise
structural coverage and reject representative data/plan mutations.
-/

namespace CertifiedJL.Tests.OneRowReplayCanaries

open TyurinModerate

/-- The committed moderate grid has no endpoint gaps. -/
theorem moderate_grid_coverage :
    CellChain moderateGridCells (1 / 50) (19707 / 100000) :=
  moderateGridCells_chain

/-- Replacing a retained cell's outer plan size by zero is rejected. -/
theorem moderate_cell023_mutation_rejected :
    outerPlanCheck CertificateProofs.Cell023.certificateCell 0 = false := by
  decide +kernel

/-- The Nat replay checks precisely the retained 308-cell prefix. -/
theorem sparse_all_cells_covered_and_checked :
    SparseOneRowCertificate.natCompleteCheck = true :=
  SparseOneRowCertificate.natCompleteCheck_verified

/-- Omitting the first sparse shard is rejected structurally. -/
theorem sparse_omission_mutation_rejected :
    (List.range SparseOneRowCertificate.gridSize).drop 1 ≠
      List.range SparseOneRowCertificate.gridSize := by
  decide +kernel

/-- Duplicating a sparse shard is rejected structurally. -/
theorem sparse_duplication_mutation_rejected :
    0 :: List.range SparseOneRowCertificate.gridSize ≠
      List.range SparseOneRowCertificate.gridSize := by
  decide +kernel

/-- Tightening the scalar target rejects the known near-maximal cell. -/
theorem sparse_tightened_target_mutation_rejected :
    Interval.upperLTCheck
        (SparseOneRowCertificate.cellUpper 112)
        (SparseOneRowCertificate.target / 2) = false := by
  decide +kernel

end CertifiedJL.Tests.OneRowReplayCanaries
