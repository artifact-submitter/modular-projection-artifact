#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
output_dir="$repo_root/CertifiedJL/Certificates/Families/OneRow975/NormalApproximation/Replay/CertificateProofs"
mkdir -p "$output_dir"

for ((cell_index = 0; cell_index < 24; cell_index++)); do
  module_index=$(printf '%03d' "$cell_index")
  output="$output_dir/Cell${module_index}.lean"
  {
    printf '%s\n' '/-'
    printf '%s\n' 'Copyright (c) 2026 Anonymous Author. All rights reserved.'
    printf '%s\n' 'Released under Apache 2.0 license as described in the file LICENSE.'
    printf '%s\n' 'Authors: Anonymous Author'
    printf '%s\n\n' '-/'
    printf '%s\n' 'import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.OuterPlan'
    printf '%s\n\n' 'import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Data.Grid'
    printf '%s\n' 'namespace CertifiedJL'
    printf '%s\n' 'namespace TyurinModerate'
    printf '%s\n' 'namespace CertificateProofs'
    printf 'namespace Cell%s\n\n' "$module_index"
    printf '%s\n\n' 'set_option maxRecDepth 10000'
    printf '/-- The moderate-grid cell at index %d replayed by this shard. -/\n' "$cell_index"
    printf 'def certificateCell : Cell :=\n'
    printf '  moderateGridCells[%d]'"'"'(by decide)\n\n' "$cell_index"
    printf '%s\n' '/-- The 53-cell scaled outer plan is locally safe. -/'
    printf '%s\n' 'theorem outerPlan : outerPlanCheck certificateCell = true := by'
    printf '%s\n\n' '  decide +kernel'

    printf '%s\n' '/-- The generated scaled-coordinate certificate semantically certifies this grid cell. -/'
    printf '%s\n' 'theorem cellCertified : CellCertified certificateCell := by'
    if ((cell_index < 20)); then
    printf '%s\n' '  apply cellCertified_of_closedCore_outerPlan'
    printf '%s\n' '  · decide +kernel'
    printf '%s\n' '  · decide +kernel'
    printf '%s\n' '  · decide +kernel'
    printf '%s\n' '  · decide +kernel'
    printf '%s\n' '  · exact outerPlan'
    printf '%s\n\n' '  · decide +kernel'
    else
    printf '%s\n' '  apply cellCertified_of_crossingCore_outerPlan'
    printf '%s\n' '  · decide +kernel'
    printf '%s\n' '  · decide +kernel'
    printf '%s\n' '  · decide +kernel'
    printf '%s\n' '  · exact outerPlan'
    printf '%s\n\n' '  · decide +kernel'
    fi

    printf 'end Cell%s\n' "$module_index"
    printf '%s\n' 'end CertificateProofs'
    printf '%s\n' 'end TyurinModerate'
    printf '%s\n' 'end CertifiedJL'
  } > "$output"
done

assembly="$repo_root/CertifiedJL/Certificates/Families/OneRow975/NormalApproximation/Replay/CertificateProofs.lean"
{
  printf '%s\n' '/-'
  printf '%s\n' 'Copyright (c) 2026 Anonymous Author. All rights reserved.'
  printf '%s\n' 'Released under Apache 2.0 license as described in the file LICENSE.'
  printf '%s\n' 'Authors: Anonymous Author'
  printf '%s\n\n' '-/'
  for ((cell_index = 0; cell_index < 24; cell_index++)); do
    module_index=$(printf '%03d' "$cell_index")
    printf 'import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs.Cell%s\n' \
      "$module_index"
  done
  printf '%s\n\n' 'import Mathlib.Tactic.IntervalCases'
  printf '%s\n' '/-!'
  printf '%s\n' '# Complete moderate-Lyapunov certificate replay'
  printf '%s\n'
  printf '%s\n' 'This module imports the 24 independent proof shards and assembles their'
  printf '%s\n' 'semantic cell certificates.  Each expensive interval computation is reduced'
  printf '%s\n' 'in its own module; the proofs here perform only finite index bookkeeping.'
  printf '%s\n\n' '-/'
  printf '%s\n' 'namespace CertifiedJL'
  printf '%s\n\n' 'namespace TyurinModerate'
  printf '%s\n\n' 'set_option maxRecDepth 10000'
  printf '%s\n' '/-- Every indexed member of the committed moderate grid is certified. -/'
  printf '%s\n' 'theorem moderateGridCellCertified'
  printf '%s\n' '    (index : ℕ) (hindex : index < moderateGridCells.length) :'
  printf '%s\n' '    CellCertified moderateGridCells[index] := by'
  printf '%s\n' '  rw [moderateGridCells_length] at hindex'
  printf '%s\n' '  interval_cases index'
  for ((cell_index = 0; cell_index < 24; cell_index++)); do
    module_index=$(printf '%03d' "$cell_index")
    printf '  · exact CertificateProofs.Cell%s.cellCertified\n' "$module_index"
  done
  printf '%s\n'
  printf '%s\n' '/-- Every member of the committed moderate grid is semantically certified. -/'
  printf '%s\n' 'theorem moderateGridCells_certified'
  printf '%s\n' '    (C : Cell) (hC : C ∈ moderateGridCells) : CellCertified C := by'
  printf '%s\n' '  obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hC'
  printf '%s\n\n' '  exact moderateGridCellCertified index hindex'
  printf '%s\n' 'end TyurinModerate'
  printf '%s\n' 'end CertifiedJL'
} > "$assembly"
