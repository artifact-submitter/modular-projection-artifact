/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Soundness

/-!
# Coverage assembly for the moderate-Lyapunov certificate

This module separates two logically different obligations:

* `CellChain` records that closed rational cells meet endpoint-to-endpoint;
* `cellCheck C = true` records the analytic and numerical proof for each cell.

The final theorem combines those obligations and chooses valid Prawitz cutoffs
for every real Lyapunov parameter in the covered interval.
-/

namespace CertifiedJL
namespace TyurinModerate

open Probability

/--
`CellChain cells a b` means that `cells` is a nonempty, ordered chain of
closed cells starting at `a` and ending at `b`, with consecutive endpoints
equal.  This representation makes the coverage proof structural and keeps
endpoint bookkeeping independent of expensive cell evaluation.
-/
inductive CellChain : List Cell → ℚ → ℚ → Prop
  | single (C : Cell) : CellChain [C] C.lo C.hi
  | cons (C : Cell) {cells : List Cell} {a b : ℚ} :
      CellChain cells a b →
      C.hi = a →
      CellChain (C :: cells) C.lo b

/-- Executable adjacency and endpoint check for a nonempty cell chain. -/
def cellChainCheck : List Cell → ℚ → ℚ → Bool
  | [], _, _ => false
  | [C], a, b => decide (C.lo = a ∧ C.hi = b)
  | C :: D :: cells, a, b =>
      decide (C.lo = a ∧ C.hi = D.lo) &&
        cellChainCheck (D :: cells) D.lo b

/-- The executable adjacency check produces the semantic chain relation. -/
theorem cellChainCheck_sound
    {cells : List Cell} {a b : ℚ}
    (hcheck : cellChainCheck cells a b = true) :
    CellChain cells a b := by
  induction cells generalizing a b with
  | nil =>
      simp [cellChainCheck] at hcheck
  | cons C cells ih =>
      cases cells with
      | nil =>
          have hends : C.lo = a ∧ C.hi = b := by
            exact of_decide_eq_true (by
              simpa [cellChainCheck] using hcheck)
          simpa [hends.1, hends.2] using CellChain.single C
      | cons D cells =>
          unfold cellChainCheck at hcheck
          rw [Bool.and_eq_true] at hcheck
          have hjoin : C.lo = a ∧ C.hi = D.lo :=
            of_decide_eq_true hcheck.1
          have htail :
              CellChain (D :: cells) D.lo b :=
            ih hcheck.2
          simpa [hjoin.1] using
            CellChain.cons C htail hjoin.2

/--
Every real point in the closed interval spanned by a cell chain belongs to
at least one member cell.
-/
theorem CellChain.exists_mem
    {cells : List Cell} {a b : ℚ}
    (hchain : CellChain cells a b)
    {L : ℝ} (ha : (a : ℝ) ≤ L) (hb : L ≤ (b : ℝ)) :
    ∃ C ∈ cells, (C.lo : ℝ) ≤ L ∧ L ≤ (C.hi : ℝ) := by
  induction hchain with
  | single C =>
      exact ⟨C, by simp, ha, hb⟩
  | @cons C cells a b htail hjoin ih =>
      by_cases hleft : L ≤ (C.hi : ℝ)
      · exact ⟨C, by simp, ha, hleft⟩
      · have htailLeft : (a : ℝ) ≤ L := by
          have hjoinReal : (C.hi : ℝ) = (a : ℝ) := by
            exact_mod_cast hjoin
          rw [← hjoinReal]
          exact le_of_not_ge hleft
        obtain ⟨D, hDmem, hDlo, hDhi⟩ :=
          ih htailLeft hb
        exact ⟨D, by simp [hDmem], hDlo, hDhi⟩

/--
Semantic property required from each member of a certified cell cover.
It is intentionally independent of the concrete reflection strategy.
-/
def CellCertified (C : Cell) : Prop :=
  (0 : ℝ) < C.cutoff ∧
    (C.cutoff : ℝ) ≤ C.bandwidth ∧
    ∀ {L : ℝ}, (C.lo : ℝ) ≤ L → L ≤ (C.hi : ℝ) →
      tyurinRationalDStar L
        (C.cutoff : ℝ) (C.bandwidth : ℝ) < 3 / 5

/--
A semantically certified chain supplies concrete cutoffs throughout its
covered interval.  Chunked and monolithic certificate evaluators share this
same final assembly theorem.
-/
theorem exists_cutoffs_of_cellChain_of_certified
    {cells : List Cell} {a b : ℚ}
    (hchain : CellChain cells a b)
    (hcertified : ∀ C ∈ cells, CellCertified C)
    {L : ℝ} (ha : (a : ℝ) ≤ L) (hb : L ≤ (b : ℝ)) :
    ∃ C ∈ cells,
      (0 : ℝ) < C.cutoff ∧
        (C.cutoff : ℝ) ≤ C.bandwidth ∧
        tyurinRationalDStar L
            (C.cutoff : ℝ) (C.bandwidth : ℝ) < 3 / 5 := by
  obtain ⟨C, hCmem, hClo, hChi⟩ :=
    hchain.exists_mem ha hb
  rcases hcertified C hCmem with ⟨hcutoff, hcut, hDStar⟩
  exact ⟨C, hCmem, hcutoff, hcut, hDStar hClo hChi⟩

/-- A successful monolithic cell check is one producer of `CellCertified`. -/
theorem cellCertified_of_cellCheck
    {C : Cell} (hcheck : cellCheck C = true) :
    CellCertified C := by
  have hgeometry : geometryCheck C = true := by
    unfold cellCheck at hcheck
    rw [Bool.and_eq_true] at hcheck
    rw [Bool.and_eq_true] at hcheck
    exact hcheck.1.1
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, hcutoff, hcut, _⟩
  refine ⟨by exact_mod_cast hcutoff,
    by exact_mod_cast hcut, ?_⟩
  intro L hL hLb
  exact tyurinRationalDStar_lt_three_fifths_of_cell
    hcheck hL hLb

/--
Convenience corollary for small cells whose complete Boolean checker is
cheap enough to replay directly.
-/
theorem exists_cutoffs_of_cellChain
    {cells : List Cell} {a b : ℚ}
    (hchain : CellChain cells a b)
    (hchecked : ∀ C ∈ cells, cellCheck C = true)
    {L : ℝ} (ha : (a : ℝ) ≤ L) (hb : L ≤ (b : ℝ)) :
    ∃ C ∈ cells,
      (0 : ℝ) < C.cutoff ∧
        (C.cutoff : ℝ) ≤ C.bandwidth ∧
        tyurinRationalDStar L
            (C.cutoff : ℝ) (C.bandwidth : ℝ) < 3 / 5 :=
  exists_cutoffs_of_cellChain_of_certified hchain
    (fun C hC => cellCertified_of_cellCheck (hchecked C hC))
    ha hb

end TyurinModerate
end CertifiedJL
