/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128Selector

/-! # Reusable analytic row caps for the ten-cell singleton-Fourier cover -/

namespace CertifiedJL.SparseThresholdDominant.SingletonFourierCover128

open SingletonFourierNumeric128

theorem cells_certified : cells.all certifiedCheck = true := by
  simp [cells, cell00_certified, cell01_certified, cell02_certified,
    cell03_certified, cell04_certified, cell05_certified, cell06_certified,
    cell07_certified, cell08_certified, cell09_certified]

/-- The expensive analytic row enclosures, replayed once for all later targets. -/
theorem cells_safe : cells.all safeCheck = true := by
  have hcertified := cells_certified
  rw [List.all_eq_true] at hcertified ⊢
  intro cell hmem
  exact safeCheck_of_certifiedCheck (hcertified cell hmem)

end CertifiedJL.SparseThresholdDominant.SingletonFourierCover128
