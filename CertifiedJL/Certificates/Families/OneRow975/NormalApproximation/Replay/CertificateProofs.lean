/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell000
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell001
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell002
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell003
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell004
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell005
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell006
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell007
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell008
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell009
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell010
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell011
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell012
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell013
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell014
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell015
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell016
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell017
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell018
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell019
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell020
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell021
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell022
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell023
import Mathlib.Tactic.IntervalCases

/-!
# Complete moderate-Lyapunov certificate replay

This module imports the 24 independent proof shards and assembles their
semantic cell certificates.  Each expensive interval computation is reduced
in its own module; the proofs here perform only finite index bookkeeping.
-/

namespace CertifiedJL
namespace TyurinModerate

set_option maxRecDepth 10000

/-- Every indexed member of the committed moderate grid is certified. -/
theorem moderateGridCellCertified
    (index : ℕ) (hindex : index < moderateGridCells.length) :
    CellCertified moderateGridCells[index] := by
  rw [moderateGridCells_length] at hindex
  interval_cases index
  · exact CertificateProofs.Cell000.cellCertified
  · exact CertificateProofs.Cell001.cellCertified
  · exact CertificateProofs.Cell002.cellCertified
  · exact CertificateProofs.Cell003.cellCertified
  · exact CertificateProofs.Cell004.cellCertified
  · exact CertificateProofs.Cell005.cellCertified
  · exact CertificateProofs.Cell006.cellCertified
  · exact CertificateProofs.Cell007.cellCertified
  · exact CertificateProofs.Cell008.cellCertified
  · exact CertificateProofs.Cell009.cellCertified
  · exact CertificateProofs.Cell010.cellCertified
  · exact CertificateProofs.Cell011.cellCertified
  · exact CertificateProofs.Cell012.cellCertified
  · exact CertificateProofs.Cell013.cellCertified
  · exact CertificateProofs.Cell014.cellCertified
  · exact CertificateProofs.Cell015.cellCertified
  · exact CertificateProofs.Cell016.cellCertified
  · exact CertificateProofs.Cell017.cellCertified
  · exact CertificateProofs.Cell018.cellCertified
  · exact CertificateProofs.Cell019.cellCertified
  · exact CertificateProofs.Cell020.cellCertified
  · exact CertificateProofs.Cell021.cellCertified
  · exact CertificateProofs.Cell022.cellCertified
  · exact CertificateProofs.Cell023.cellCertified

/-- Every member of the committed moderate grid is semantically certified. -/
theorem moderateGridCells_certified
    (C : Cell) (hC : C ∈ moderateGridCells) : CellCertified C := by
  obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hC
  exact moderateGridCellCertified index hindex

end TyurinModerate
end CertifiedJL
