import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ConstantNumeric
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard00
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard01
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard02
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard03
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard04
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard05
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard06
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard07
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard08
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard09
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard10
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard11
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard12
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard13
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard14
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard15
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard16
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard17
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard18
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard19
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard20
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard21
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard22
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard23
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard24
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard25
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard26
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard27
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard28
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard29
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard30
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard31
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard32
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard33
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard34
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard35
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard36
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard37
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard38
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard39
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard40
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard41
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard42
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard43
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard44
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard45
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard46

/-! # Exact aggregate of the independent 128-bit direct-cover shards -/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Aggregate

open ConstantNumeric

@[simp] theorem entriesValidCheck_append (xs ys : List Entry) :
    entriesValidCheck (xs ++ ys) =
      (entriesValidCheck xs && entriesValidCheck ys) := by
  simp [entriesValidCheck]

@[simp] theorem entriesCertifiedCheckAt_append
    (xs ys : List Entry) (budget : ℚ) :
    entriesCertifiedCheckAt (xs ++ ys) budget =
      (entriesCertifiedCheckAt xs budget &&
        entriesCertifiedCheckAt ys budget) := by
  simp [entriesCertifiedCheckAt]

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Aggregate

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard00

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry := entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simpa [allEntries] using entries_valid

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simpa [allEntries] using entries_certified

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard00

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard01

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard00.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard00.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard00.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard01

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard02

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard01.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard01.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard01.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard02

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard03

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard02.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard02.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard02.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard03

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard04

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard03.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard03.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard03.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard04

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard05

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard04.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard04.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard04.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard05

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard06

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard05.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard05.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard05.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard06

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard07

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard06.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard06.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard06.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard07

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard08

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard07.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard07.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard07.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard08

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard09

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard08.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard08.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard08.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard09

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard10

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard09.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard09.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard09.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard10

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard11

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard10.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard10.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard10.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard11

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard12

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard11.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard11.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard11.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard12

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard13

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard12.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard12.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard12.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard13

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard14

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard13.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard13.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard13.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard14

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard15

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard14.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard14.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard14.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard15

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard16

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard15.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard15.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard15.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard16

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard17

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard16.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard16.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard16.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard17

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard18

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard17.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard17.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard17.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard18

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard19

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard18.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard18.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard18.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard19

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard20

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard19.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard19.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard19.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard20

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard21

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard20.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard20.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard20.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard21

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard22

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard21.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard21.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard21.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard22

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard23

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard22.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard22.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard22.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard23

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard24

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard23.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard23.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard23.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard24

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard25

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard24.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard24.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard24.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard25

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard26

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard25.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard25.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard25.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard26

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard27

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard26.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard26.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard26.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard27

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard28

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard27.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard27.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard27.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard28

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard29

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard28.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard28.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard28.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard29

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard30

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard29.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard29.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard29.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard30

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard31

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard30.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard30.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard30.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard31

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard32

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard31.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard31.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard31.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard32

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard33

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard32.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard32.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard32.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard33

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard34

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard33.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard33.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard33.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard34

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard35

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard34.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard34.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard34.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard35

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard36

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard35.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard35.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard35.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard36

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard37

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard36.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard36.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard36.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard37

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard38

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard37.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard37.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard37.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard38

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard39

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard38.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard38.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard38.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard39

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard40

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard39.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard39.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard39.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard40

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard41

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard40.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard40.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard40.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard41

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard42

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard41.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard41.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard41.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard42

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard43

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard42.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard42.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard42.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard43

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard44

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard43.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard43.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard43.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard44

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard45

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard44.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard44.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard44.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard45

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard46

open ConstantNumeric

theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))
    entries_valid entries_certified hmem

def allEntries : List Entry :=
  ConstantDirectCover128Shard45.allEntries ++ entries

theorem allEntries_valid_check :
    entriesValidCheck allEntries = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesValidCheck_append,
    ConstantDirectCover128Shard45.allEntries_valid_check, entries_valid]
  decide

theorem allEntries_certified_check :
    entriesCertifiedCheckAt allEntries
      (187 / (200 * 2 ^ 128)) = true := by
  simp only [allEntries,
    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,
    ConstantDirectCover128Shard45.allEntries_certified_check, entries_certified]
  decide

theorem allEntries_valid {entry : Entry}
    (hmem : entry ∈ allEntries) : entry.cell.Valid := by
  have hvalid := allEntries_valid_check
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  exact (entryValidCheck_sound (hvalid entry hmem)).1

theorem allEntries_bound {entry : Entry}
    (hmem : entry ∈ allEntries) :
    thresholdDominantCellMajorant entry.cell.decode <
      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))
    allEntries_valid_check allEntries_certified_check hmem

theorem allEntries_length : allEntries.length = 188 := by
  decide +kernel

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Shard46
