/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.Numeric
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.TargetNumericData
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Intervals

/-! Executable direct-cell certificates and rational specification equalities.
No probability soundness or generated replay is imported here. -/

namespace CertifiedJL.SparseThresholdDominant.ConstantNumeric
open DominantNumeric SparseThresholdDominant.Numeric

abbrev DInterval := DominantNumeric.DInterval

/-- A direct dominant rectangle with one tilt shared by all activity counts. -/
structure Cell where
  lower : ℚ
  upper : ℚ
  thresholdUpper : ℚ
  modulusLower : ℚ
  z : ℚ
deriving DecidableEq

def Cell.decode (cell : Cell) : ThresholdDominantCellRowBounds where
  lower := cell.lower
  upper := cell.upper
  thresholdUpper := cell.thresholdUpper
  modulusLower := cell.modulusLower
  z := fun _ => cell.z

def Cell.Valid (cell : Cell) : Prop :=
  cell.decode.Valid ∧ 0 < cell.z

/-- Small rational upper endpoints carried by a constant-cell certificate. -/
structure Certificate where
  inactiveUpper : ℚ
  activeUpper : ℚ
  growthUpper : ℚ
deriving DecidableEq

def Certificate.Valid (certificate : Certificate) : Prop :=
  0 ≤ certificate.inactiveUpper ∧
    0 ≤ certificate.activeUpper ∧ 0 ≤ certificate.growthUpper

/-- A cell paired with its compressed rational certificate. -/
structure Entry where
  cell : Cell
  certificate : Certificate

/-- One shared interval enclosure for the public-threshold exponential. -/
def growthInterval (cell : Cell) : DInterval :=
  powNat
    (expUpper (rat (29 * cell.z * cell.thresholdUpper / 256))) 256

def conditionalUpper (certificate : Certificate) (k : Fin 257) : ℚ :=
  if (k : ℕ) < 29 then 0
  else min 1
    (certificate.growthUpper * certificate.activeUpper ^ (k : ℕ) *
      certificate.inactiveUpper ^ (256 - (k : ℕ)))

/-- Exact binomial average evaluated with the factorial-based implementation
of the binomial coefficient and a single common power-of-two denominator. -/
def binomialAverageRat (rows : ℕ) (term : Fin (rows + 1) → ℚ) : ℚ :=
  (List.ofFn fun k => ((Nat.fast_choose rows (k : ℕ) : ℕ) : ℚ) * term k).sum /
    2 ^ rows

private theorem list_sum_div (xs : List ℚ) (d : ℚ) :
    xs.sum / d = (xs.map fun x => x / d).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.sum_cons, List.map_cons, ih, add_div]

/-- The fast rational evaluator is exactly the ordinary binomial average. -/
theorem binomialAverageRat_eq (rows : ℕ) (term : Fin (rows + 1) → ℚ) :
    binomialAverageRat rows term =
      (List.ofFn fun k =>
        (((rows.choose (k : ℕ) : ℕ) : ℚ) / 2 ^ rows) * term k).sum := by
  rw [binomialAverageRat, list_sum_div]
  simp only [List.ofFn_eq_map, List.map_map, Nat.choose_eq_fast_choose,
    div_eq_mul_inv]
  congr 1
  apply List.map_congr_left
  intro k _
  dsimp
  ring

def majorantUpper (certificate : Certificate) : ℚ :=
  binomialAverageRat 256 (conditionalUpper certificate)

/-! ## Bounded prefix plus geometric tail evaluation -/

/-- A compact witness for replacing a long exact binomial sum by an exact
prefix and a certified geometric remainder. -/
structure GeometricTailCertificate where
  prefixTerms : ℕ
  ratioUpper : ℚ
deriving DecidableEq

/-- The untruncated weighted binomial term.  Keeping `fast_choose` here is
important: the witness checker evaluates only the prefix and the first tail
term, but those few coefficients should still use the efficient executable
implementation. -/
def weightedRawTermRat (rows : ℕ) (growth active inactive : ℚ) (k : ℕ) : ℚ :=
  ((Nat.fast_choose rows k : ℕ) : ℚ) * growth * active ^ k *
    inactive ^ (rows - k) / 2 ^ rows

/-- The weighted term of the original, truncated conditional majorant. -/
def weightedConditionalTermRat (rows squaredNormFloor : ℕ)
    (growth active inactive : ℚ) (k : ℕ) : ℚ :=
  ((Nat.fast_choose rows k : ℕ) : ℚ) *
    (if k < squaredNormFloor then 0
      else min 1 (growth * active ^ k * inactive ^ (rows - k))) /
    2 ^ rows

/-- Exact short prefix followed by the infinite geometric upper bound rooted
at the first omitted weighted term. -/
def prefixGeometricUpperRat (rows squaredNormFloor : ℕ)
    (growth active inactive : ℚ) (tail : GeometricTailCertificate) : ℚ :=
  let tailStart := squaredNormFloor + tail.prefixTerms
  (Finset.Ico squaredNormFloor tailStart).sum (fun k =>
      weightedConditionalTermRat rows squaredNormFloor growth active inactive k) +
    weightedRawTermRat rows growth active inactive tailStart /
      (1 - tail.ratioUpper)

/-- Prefix/geometric evaluator specialized to the original 256-row checker. -/
def prefixGeometricUpper (certificate : Certificate)
    (tail : GeometricTailCertificate) : ℚ :=
  prefixGeometricUpperRat 256 29 certificate.growthUpper
    certificate.activeUpper certificate.inactiveUpper tail

/-- The target-independent row enclosure certified by a direct-cell entry. -/
def RowCapsCertified (cell : Cell) (certificate : Certificate) : Prop :=
    inactiveRowSafeCheck cell.decode cell.z = true ∧
    activeRowSafeCheck cell.decode cell.z = true ∧
    (inactiveRow cell.decode cell.z).upperRat ≤
      certificate.inactiveUpper ∧
    (activeRow cell.decode cell.z).upperRat ≤
      certificate.activeUpper ∧
    0 ≤ (inactiveRow cell.decode cell.z).lo ∧
    0 ≤ (activeRow cell.decode cell.z).lo

/-- Executable checker for the target-independent direct-cell row caps. -/
def rowCapsCheck (cell : Cell) (certificate : Certificate) : Bool :=
  let _ : Decidable (RowCapsCertified cell certificate) := by
    unfold RowCapsCertified
    infer_instance
  decide (RowCapsCertified cell certificate)

/-- A checked row-cap record is the corresponding reusable proposition. -/
theorem rowCapsCheck_sound (cell : Cell) (certificate : Certificate)
    (hcheck : rowCapsCheck cell certificate = true) :
    RowCapsCertified cell certificate := by
  let _ : Decidable (RowCapsCertified cell certificate) := by
    unfold RowCapsCertified
    infer_instance
  simpa only [rowCapsCheck] using of_decide_eq_true hcheck

/-- The target-specific part of the original 256-row replay. -/
def localTargetCheckAt (cell : Cell) (certificate : Certificate)
    (budget : ℚ) : Bool :=
  decide (
    (rat (29 * cell.z * cell.thresholdUpper / 256)).upperRat ≤ 1 ∧
    (growthInterval cell).upperRat ≤ certificate.growthUpper ∧
    majorantUpper certificate < budget)

/-- The expensive row intervals are a separate reusable certificate; this
checker retains exactly the conjunction checked by the original replay. -/
def localCertifiedCheckAt (cell : Cell) (certificate : Certificate)
    (budget : ℚ) : Bool :=
  rowCapsCheck cell certificate && localTargetCheckAt cell certificate budget

/-- Cheaper alternative to `localCertifiedCheckAt`.  It checks a short exact
prefix and one rational ratio witness instead of normalizing all 257 weighted
terms. -/
def localCertifiedGeometricCheckAt (cell : Cell) (certificate : Certificate)
    (tail : GeometricTailCertificate) (budget : ℚ) : Bool :=
  let tailStart := 29 + tail.prefixTerms
  decide (
    inactiveRowSafeCheck cell.decode cell.z = true ∧
    activeRowSafeCheck cell.decode cell.z = true ∧
    (inactiveRow cell.decode cell.z).upperRat ≤ certificate.inactiveUpper ∧
    (activeRow cell.decode cell.z).upperRat ≤ certificate.activeUpper ∧
    0 ≤ (inactiveRow cell.decode cell.z).lo ∧
    0 ≤ (activeRow cell.decode cell.z).lo ∧
    (rat (29 * cell.z * cell.thresholdUpper / 256)).upperRat ≤ 1 ∧
    (growthInterval cell).upperRat ≤ certificate.growthUpper ∧
    tailStart ≤ 256 ∧
    0 < certificate.inactiveUpper ∧
    0 ≤ certificate.activeUpper ∧
    0 ≤ tail.ratioUpper ∧ tail.ratioUpper < 1 ∧
    (256 - tailStart) * certificate.activeUpper ≤
      tail.ratioUpper * (tailStart + 1) * certificate.inactiveUpper ∧
    prefixGeometricUpper certificate tail < budget)

/-! ## Row-count and squared-norm-floor generic replay -/

/-- Decode the dimensionless cell geometry at an arbitrary row count. -/
def Cell.decodeAt (rows : ℕ) (cell : Cell) :
    ThresholdDominantCellRowBoundsAt rows where
  lower := cell.lower
  upper := cell.upper
  thresholdUpper := cell.thresholdUpper
  modulusLower := cell.modulusLower
  z := fun _ => cell.z

theorem Cell.validAt (rows : ℕ) {cell : Cell} (hcell : cell.Valid) :
    (cell.decodeAt rows).Valid := by
  exact ⟨hcell.1.1, hcell.1.2.1, hcell.1.2.2.1, hcell.1.2.2.2.1,
    fun _ => hcell.2.le⟩

/-- Target-dependent enclosure of the complete public-threshold exponential. -/
def growthIntervalAt (rows squaredNormFloor : ℕ) (cell : Cell) : DInterval :=
  TargetNumeric.growthIntervalAt rows squaredNormFloor cell.z cell.thresholdUpper

def conditionalUpperAt (rows squaredNormFloor : ℕ) (cell : Cell)
    (certificate : Certificate) (k : Fin (rows + 1)) : ℚ :=
  if (k : ℕ) < squaredNormFloor then 0
  else min 1
    ((growthIntervalAt rows squaredNormFloor cell).upperRat *
      certificate.activeUpper ^ (k : ℕ) *
      certificate.inactiveUpper ^ (rows - (k : ℕ)))

def majorantUpperAt (rows squaredNormFloor : ℕ) (cell : Cell)
    (certificate : Certificate) : ℚ :=
  binomialAverageRat rows
    (conditionalUpperAt rows squaredNormFloor cell certificate)

/-- Target-dependent prefix/geometric upper bound. -/
def prefixGeometricUpperAt (rows squaredNormFloor : ℕ) (cell : Cell)
    (certificate : Certificate) (tail : GeometricTailCertificate) : ℚ :=
  prefixGeometricUpperRat rows squaredNormFloor
    (growthIntervalAt rows squaredNormFloor cell).upperRat
    certificate.activeUpper certificate.inactiveUpper tail

/-- The genuinely target-dependent part of a generic direct-cell replay. -/
def localTargetCheckFor (rows squaredNormFloor : ℕ) (cell : Cell)
    (certificate : Certificate) (budget : ℚ) : Bool :=
  decide (
    0 < rows ∧
    (rat (squaredNormFloor * cell.z * cell.thresholdUpper / rows)).upperRat ≤ 1 ∧
    majorantUpperAt rows squaredNormFloor cell certificate < budget)

/-- The generic checker composes a reusable row-cap certificate with only the
target-dependent growth factor and binomial average. -/
def localCertifiedCheckFor (rows squaredNormFloor : ℕ) (cell : Cell)
    (certificate : Certificate) (budget : ℚ) : Bool :=
  rowCapsCheck cell certificate &&
    localTargetCheckFor rows squaredNormFloor cell certificate budget

/-- Target-dependent prefix/geometric checker with the same semantic budget as
`localCertifiedCheckFor`. -/
def localCertifiedGeometricCheckFor (rows squaredNormFloor : ℕ) (cell : Cell)
    (certificate : Certificate) (tail : GeometricTailCertificate)
    (budget : ℚ) : Bool :=
  let tailStart := squaredNormFloor + tail.prefixTerms
  let growth := (growthIntervalAt rows squaredNormFloor cell).upperRat
  decide (
    0 < rows ∧
    inactiveRowSafeCheck cell.decode cell.z = true ∧
    activeRowSafeCheck cell.decode cell.z = true ∧
    (inactiveRow cell.decode cell.z).upperRat ≤ certificate.inactiveUpper ∧
    (activeRow cell.decode cell.z).upperRat ≤ certificate.activeUpper ∧
    0 ≤ (inactiveRow cell.decode cell.z).lo ∧
    0 ≤ (activeRow cell.decode cell.z).lo ∧
    (rat (squaredNormFloor * cell.z * cell.thresholdUpper / rows)).upperRat ≤ 1 ∧
    tailStart ≤ rows ∧
    0 ≤ growth ∧
    0 < certificate.inactiveUpper ∧
    0 ≤ certificate.activeUpper ∧
    0 ≤ tail.ratioUpper ∧ tail.ratioUpper < 1 ∧
    (rows - tailStart) * certificate.activeUpper ≤
      tail.ratioUpper * (tailStart + 1) * certificate.inactiveUpper ∧
    prefixGeometricUpperAt rows squaredNormFloor cell certificate tail < budget)

def entryValidCheck (entry : Entry) : Bool :=
  decide (0 ≤ entry.cell.lower ∧ entry.cell.lower ≤ entry.cell.upper ∧
    0 ≤ entry.cell.thresholdUpper ∧ 1 < entry.cell.modulusLower ∧
    0 < entry.cell.z ∧ 0 ≤ entry.certificate.inactiveUpper ∧
    0 ≤ entry.certificate.activeUpper ∧ 0 ≤ entry.certificate.growthUpper)

theorem entryValidCheck_sound {entry : Entry}
    (hcheck : entryValidCheck entry = true) :
    entry.cell.Valid ∧ entry.certificate.Valid := by
  have h := of_decide_eq_true (by simpa only [entryValidCheck] using hcheck)
  refine ⟨⟨?_, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ => h.2.2.2.2.1.le⟩

def entriesValidCheck (entries : List Entry) : Bool :=
  entries.all entryValidCheck

def entriesCertifiedCheckAt (entries : List Entry) (budget : ℚ) : Bool :=
  entries.all fun entry =>
    localCertifiedCheckAt entry.cell entry.certificate budget

def entriesRowCapsCheck (entries : List Entry) : Bool :=
  entries.all fun entry => rowCapsCheck entry.cell entry.certificate

def entriesLocalTargetCheckAt (entries : List Entry) (budget : ℚ) : Bool :=
  entries.all fun entry =>
    localTargetCheckAt entry.cell entry.certificate budget

theorem entriesCertifiedCheckAt_of_checks (entries : List Entry) (budget : ℚ)
    (hcaps : entriesRowCapsCheck entries = true)
    (htarget : entriesLocalTargetCheckAt entries budget = true) :
    entriesCertifiedCheckAt entries budget = true := by
  rw [entriesRowCapsCheck, List.all_eq_true] at hcaps
  rw [entriesLocalTargetCheckAt, List.all_eq_true] at htarget
  rw [entriesCertifiedCheckAt, List.all_eq_true]
  intro entry hmem
  simp only [localCertifiedCheckAt, hcaps entry hmem,
    htarget entry hmem, Bool.true_and]

/-- Transport a base row-cap replay across definitionally or computationally
verified cell/certificate reuse. This comparison is cheap: it never unfolds
either interval evaluator. -/
theorem all_rowCapsCheck_of_eq (entries : List Entry)
    (cellFor : Entry → Cell) (certificateFor : Entry → Certificate)
    (hcells : entries.all (fun entry => decide (cellFor entry = entry.cell)) = true)
    (hcertificates : entries.all (fun entry =>
      decide (certificateFor entry = entry.certificate)) = true)
    (hcaps : entriesRowCapsCheck entries = true) :
    entries.all (fun entry =>
      rowCapsCheck (cellFor entry) (certificateFor entry)) = true := by
  rw [List.all_eq_true] at hcells hcertificates ⊢
  rw [entriesRowCapsCheck, List.all_eq_true] at hcaps
  intro entry hmem
  have hcell : cellFor entry = entry.cell := by
    exact of_decide_eq_true (hcells entry hmem)
  have hcertificate : certificateFor entry = entry.certificate := by
    exact of_decide_eq_true (hcertificates entry hmem)
  simpa only [hcell, hcertificate] using hcaps entry hmem

/-- Assemble a target replay from a reusable row-cap proof and a fresh target
check. `certificateFor` permits the few targets with deliberately tighter
caps to share their own cap proof as well. -/
theorem all_localCertifiedCheckFor_of_rowCaps (rows squaredNormFloor : ℕ)
    (entries : List Entry) (cellFor : Entry → Cell)
    (certificateFor : Entry → Certificate) (budget : ℚ)
    (hcaps : entries.all (fun entry =>
      rowCapsCheck (cellFor entry) (certificateFor entry)) = true)
    (htarget : entries.all (fun entry =>
      localTargetCheckFor rows squaredNormFloor (cellFor entry)
        (certificateFor entry) budget) = true) :
    entries.all (fun entry =>
      localCertifiedCheckFor rows squaredNormFloor (cellFor entry)
        (certificateFor entry) budget) = true := by
  rw [List.all_eq_true] at hcaps htarget ⊢
  intro entry hmem
  simp only [localCertifiedCheckFor, hcaps entry hmem,
    htarget entry hmem, Bool.true_and]

def entriesCertifiedCheckFor (rows squaredNormFloor : ℕ)
    (entries : List Entry) (budget : ℚ) : Bool :=
  entries.all fun entry =>
    localCertifiedCheckFor rows squaredNormFloor entry.cell entry.certificate budget

end CertifiedJL.SparseThresholdDominant.ConstantNumeric
