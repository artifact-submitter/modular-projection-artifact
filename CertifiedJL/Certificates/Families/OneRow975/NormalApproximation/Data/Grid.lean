/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.Core

/-!
# Moderate-Lyapunov certificate grid

This module records the exact rational cell grid covering
`[1/50, 19707/100000]`.  This is the complete moderate range needed by the
fixed-threshold sparse one-row theorem after its fourth-moment profile split.
It contains the exact configuration and two cheap structural checks. Analytic
soundness, reflected chunk proofs, and interval coverage are kept in separate
modules.
-/

namespace CertifiedJL
namespace TyurinModerate

/-- Seven exact Newton steps used for a rational cube-root upper bracket. -/
def gridCubeRootUpper (q : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      let x := gridCubeRootUpper q n
      (2 * x + q / x ^ 2) / 3

/-- Prawitz core cutoff selected from a cell's right endpoint. -/
def gridCutoff (hi : ℚ) : ℚ :=
  if hi ≤ 12 / 25 then min (16 / 5) (17 / 5 - hi)
  else if hi ≤ 7 / 10 then 167 / 50 - hi
  else 49 / 20

/-- Numerator of the bandwidth `gridScale hi / hi`. -/
def gridScale (hi : ℚ) : ℚ :=
  if hi ≤ 3 / 10 then 31 / 10
  else if hi ≤ 2 / 5 then 3
  else if hi ≤ 12 / 25 then 73 / 25
  else 29 / 10

/-- Core and outer rectangle counts selected from a cell's right endpoint. -/
def gridCounts (hi : ℚ) : ℕ × ℕ :=
  if hi ≤ 3 / 10 then (300, 500)
  else if hi ≤ 2 / 5 then (350, 600)
  else if hi ≤ 12 / 25 then (500, 1000)
  else if hi ≤ 31 / 50 then (600, 1800)
  else if hi ≤ 7 / 10 then (500, 1200)
  else (400, 1000)

/-- Construct one exact moderate-Lyapunov cell. -/
def gridCell (lo hi : ℚ) : Cell :=
  let rootHi := gridCubeRootUpper hi 7
  let counts := gridCounts hi
  { lo := lo
    hi := hi
    cutoff := gridCutoff hi
    bandwidth := gridScale hi / hi
    rootLo := hi / rootHi ^ 2
    rootHi := rootHi
    coreCells := counts.1
    outerCells := counts.2 }

/-- Uniform consecutive cells with exact rational endpoints. -/
def uniformGridCells
    (lo step : ℚ) (count : ℕ) : List Cell :=
  (List.range count).map fun i =>
    gridCell (lo + step * i) (lo + step * (i + 1))

/-- Consecutive cells obtained from an explicit endpoint list. -/
def gridCellsFromEndpoints : List ℚ → List Cell
  | lo :: hi :: rest =>
      gridCell lo hi :: gridCellsFromEndpoints (hi :: rest)
  | _ => []

/--
Geometrically growing endpoints for the sensitive low-Lyapunov range.
-/
def lowGridEndpoints : List ℚ :=
  [2000 / 100000, 2200 / 100000, 2420 / 100000, 2662 / 100000,
    2928 / 100000, 3221 / 100000, 3543 / 100000, 3897 / 100000,
    4287 / 100000, 4716 / 100000, 5188 / 100000, 5707 / 100000,
    6278 / 100000, 6906 / 100000, 7597 / 100000, 8357 / 100000,
    9193 / 100000, 10112 / 100000, 11123 / 100000, 12235 / 100000,
    13459 / 100000, 14805 / 100000, 16286 / 100000, 17915 / 100000,
    19707 / 100000]

/-- The 24-cell one-row cover of `[1/50, 19707/100000]`. -/
def moderateGridCells : List Cell :=
  gridCellsFromEndpoints lowGridEndpoints

/-- Compact selected-envelope plan for one moderate-grid cell. -/
def moderateGridCoreChoicePlan (_cellIndex : ℕ) : CoreChoicePlan :=
  { delta := .two
    kernelInitial := .i29
    kernelSwitch := none }

/-- Selected core choice at one grid-cell/node pair. -/
def moderateGridCoreChoice
    (cellIndex nodeIndex : ℕ) : CoreChoice :=
  (moderateGridCoreChoicePlan cellIndex).at nodeIndex

theorem moderateGridCells_length :
    moderateGridCells.length = 24 := by
  decide +kernel

/-- Mutation canary: every retained one-row cell uses the I.29 kernel. -/
theorem moderateGridCoreChoice_is_i29 :
    moderateGridCoreChoice 23 299 =
      { delta := .two, kernel := .i29 } := by
  decide +kernel

end TyurinModerate
end CertifiedJL
