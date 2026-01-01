/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Pure dominant-cell bounds

This module records the scalar dominant-cell expressions shared by the
public-threshold analytic proof and its numeric certificate checker. It
imports neither finite probability models nor raw certificate data.
-/

open scoped BigOperators

namespace CertifiedJL

/-- The squared tilt parameter `H_I²(z)` from L15. -/
noncomputable def dominantCellHsq
    (lower upper z : ℚ) : ℝ :=
  let endpointLower : ℝ :=
    (z : ℝ) ^ 2 * (lower : ℝ) /
      (1 + (z : ℝ) * (lower : ℝ)) ^ 2
  let endpointUpper : ℝ :=
    (z : ℝ) ^ 2 * (upper : ℝ) /
      (1 + (z : ℝ) * (upper : ℝ)) ^ 2
  let critical : ℝ :=
    if z * lower ≤ 1 ∧ 1 ≤ z * upper then (z : ℝ) / 4 else 0
  max endpointLower (max endpointUpper critical)

/-- The row correction `bar rho_I(z)` from L15. -/
noncomputable def dominantCellRho
    (lower upper z : ℚ) : ℝ :=
  let hsq := dominantCellHsq lower upper z
  let sLower : ℝ := (z : ℝ) * (lower : ℝ)
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  min 1
    (1 - sLower / 2 * max 0 (1 - hsq) +
      3 * sUpper ^ 2 + 4 * sUpper ^ 2 * hsq ^ 2)

/-- The inactive-row nonzero modular-image majorant `P_{0,I}(z)` from L16. -/
noncomputable def dominantCellInactiveWrap
    (lower upper z : ℚ) : ℝ :=
  let B : ℝ := 3 * Real.sqrt (1 + (lower : ℝ))
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))
  2 * Real.exp (-alpha * B ^ 2) /
    (1 - Real.exp (-3 * alpha * B ^ 2))

/-- The active-row nonzero modular-image majorant `P_{1,I}(z)` from L16. -/
noncomputable def dominantCellActiveWrap
    (lower upper z : ℚ) : ℝ :=
  let B : ℝ := 3 * Real.sqrt (1 + (lower : ℝ))
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))
  Real.exp (-alpha * (B - 1) ^ 2) /
      (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
    Real.exp (-alpha * (B + 1) ^ 2) /
      (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))

/-- The complete inactive-row majorant `L_{0,I}(z)` from L17. -/
noncomputable def dominantCellInactiveRow
    (lower upper z : ℚ) : ℝ :=
  let sLower : ℝ := (z : ℝ) * (lower : ℝ)
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  let theta := Real.exp (-Real.pi ^ 2 / (1 + sUpper))
  (1 / Real.sqrt (1 + sLower)) *
      (1 + 2 * theta / (1 - theta ^ 3)) +
    dominantCellInactiveWrap lower upper z

/-- The complete active-row majorant `L_{1,I}(z)` from L17. -/
noncomputable def dominantCellActiveRow
    (lower upper z : ℚ) : ℝ :=
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  Real.exp (-(z : ℝ) / (1 + sUpper)) *
      dominantCellRho lower upper z +
    dominantCellActiveWrap lower upper z

/-- Average conditional bounds against the exact `Binomial(rows, 1/2)` mass. -/
noncomputable def dominantBinomialAverageAt
    (rows : ℕ) (Q : Fin (rows + 1) → ℝ) : ℝ :=
  ∑ k : Fin (rows + 1),
    ((rows.choose (k : ℕ) : ℝ) / 2 ^ rows) * Q k

/-- Compatibility specialization of the binomial average at 256 rows. -/
noncomputable def dominantBinomialAverage (Q : Fin 257 → ℝ) : ℝ :=
  ∑ k : Fin 257,
    (((256 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 256) * Q k

end CertifiedJL
