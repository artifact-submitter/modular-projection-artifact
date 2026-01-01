/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Coverage
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Data.Grid

/-!
# Structural coverage of the moderate-Lyapunov grid

This module proves only endpoint adjacency. The much more expensive analytic
certificate for each member cell is assembled separately.
-/

namespace CertifiedJL
namespace TyurinModerate

/-- The committed rational grid covers `[1/50,19707/100000]` without gaps. -/
theorem moderateGridCells_chain :
    CellChain moderateGridCells (1 / 50) (19707 / 100000) := by
  apply cellChainCheck_sound
  set_option maxRecDepth 10000 in
    decide +kernel

/--
Once every committed grid cell is semantically certified, the grid supplies
the exact moderate-regime premise used by the `3/5` assembly theorem.
-/
theorem moderateCutoffs_of_gridCertified
    (hcertified : ∀ C ∈ moderateGridCells, CellCertified C)
    {L : ℝ} (hlo : (1 : ℝ) / 50 ≤ L)
    (hhi : L ≤ (19707 : ℝ) / 100000) :
    ∃ U₀ U : ℝ, 0 < U₀ ∧ U₀ ≤ U ∧
      Probability.tyurinRationalDStar L U₀ U < (3 : ℝ) / 5 := by
  have hlo' : ((1 / 50 : ℚ) : ℝ) ≤ L := by
    norm_num at hlo ⊢
    exact hlo
  have hhi' : L ≤ ((19707 / 100000 : ℚ) : ℝ) := by
    norm_num at hhi ⊢
    exact hhi
  obtain ⟨C, _hCmem, hU₀, hcut, hDStar⟩ :=
    exists_cutoffs_of_cellChain_of_certified
      moderateGridCells_chain hcertified hlo' hhi'
  exact ⟨C.cutoff, C.bandwidth, hU₀, hcut, hDStar⟩

end TyurinModerate
end CertifiedJL
