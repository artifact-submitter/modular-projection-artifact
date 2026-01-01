/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.AnalyticSoundness

/-!
# Analytic-core substitution for parameterized upper contours

This module replaces an initial block of segmented quadrature cells by one
proved analytic integral bound.  The retained suffix still uses the ordinary
family Gaussian cells, and `boxIntegralFrom` supplies exactly the existing
analytic tail.  Numerical budget replay remains separate from the semantic
integral argument.
-/

open scoped ENNReal BigOperators

namespace CertifiedJL.SparseUpperContourFamily

open MeasureTheory Set

/-- Sum only the retained suffix chunks of a profile box.  This is deliberately
independent of `boxChunkPlan`: a core substitution must not evaluate discarded
prefix chunks. -/
def retainedSuffixInterval (parameters : Parameters) (box : ProfileBox) :
    List Chunk → UpperContourKernel.DInterval parameters.precision
  | [] => UpperContourKernel.zero parameters.precision
  | chunk :: rest =>
      boxChunkValue parameters box chunk +
        retainedSuffixInterval parameters box rest

/-- Literal rectangle sum represented by `retainedSuffixInterval`. -/
noncomputable def retainedSuffixRectangleValue
    (parameters : Parameters) (box : ProfileBox) : List Chunk → ℝ
  | [] => 0
  | chunk :: rest =>
      boxRectangleChunkValue parameters box chunk +
        retainedSuffixRectangleValue parameters box rest

/-- Concrete cells referenced by a selected list of retained chunks.  Unlike
`boxChunkCells`, this does not mention or evaluate the discarded prefix. -/
def retainedSuffixCells (box : ProfileBox) (suffixChunks : List Chunk) :
    List (Segment × ℕ) :=
  suffixChunks.flatMap (chunkCells box)

/-- Exact rational statement that a cell list consecutively covers `(left,
right]`.  Positivity is stored per cell, so the bridge remains sound even when
the list crosses a segment boundary or uses a partial segment. -/
def CellChain : ℚ → List (Segment × ℕ) → ℚ → Prop
  | left, [], right => left = right
  | left, cell :: rest, right =>
      0 < cell.1.mesh ∧
      cell.1.cellLeft cell.2 = left ∧
      CellChain (cell.1.cellRight cell.2) rest right

/-- Boolean form of `CellChain`, kept recursive so its decidability does not
depend on synthesizing an instance for the recursive proposition. -/
def cellChainCheck : ℚ → List (Segment × ℕ) → ℚ → Bool
  | left, [], right => decide (left = right)
  | left, cell :: rest, right =>
      decide (0 < cell.1.mesh) &&
      decide (cell.1.cellLeft cell.2 = left) &&
      cellChainCheck (cell.1.cellRight cell.2) rest right

theorem cellChainCheck_eq_true_iff
    (left : ℚ) (cells : List (Segment × ℕ)) (right : ℚ) :
    cellChainCheck left cells right = true ↔ CellChain left cells right := by
  induction cells generalizing left with
  | nil => simp [cellChainCheck, CellChain]
  | cons cell rest ih =>
      simp only [cellChainCheck, CellChain, Bool.and_eq_true,
        decide_eq_true_eq, ih]
      tauto

/-- Cheap exact geometry check for an explicitly supplied retained suffix. -/
def retainedSuffixGeometryCheck (box : ProfileBox) (coreCutoff : ℚ)
    (suffixChunks : List Chunk) : Bool :=
  cellChainCheck coreCutoff (retainedSuffixCells box suffixChunks) box.cutoff

/-- Soundness of `retainedSuffixGeometryCheck`. -/
theorem retainedSuffixGeometryCheck_sound
    {box : ProfileBox} {coreCutoff : ℚ} {suffixChunks : List Chunk}
    (hcheck : retainedSuffixGeometryCheck box coreCutoff suffixChunks = true) :
    CellChain coreCutoff (retainedSuffixCells box suffixChunks) box.cutoff := by
  exact (cellChainCheck_eq_true_iff _ _ _).mp (by
    simpa [retainedSuffixGeometryCheck] using hcheck)

private theorem foldl_add_eq_add_sum_map_coreAssembly
    {A : Type*} (xs : List A) (f : A → ℝ) (initial : ℝ) :
    xs.foldl (fun result item => result + f item) initial =
      initial + (xs.map f).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons item rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring

/-- The literal rectangle assigned to a chunk is the sum over exactly the
cells enumerated by that chunk. -/
theorem boxRectangleChunkValue_eq_chunkCells_sum
    (parameters : Parameters) (box : ProfileBox) (chunk : Chunk) :
    boxRectangleChunkValue parameters box chunk =
      ((chunkCells box chunk).map fun cell =>
        gaussianCellRectangleValue parameters box cell.1 cell.2).sum := by
  unfold boxRectangleChunkValue segmentRectangleChunkValue chunkCells
  rw [foldl_add_eq_add_sum_map_coreAssembly]
  simp [Function.comp_def]

/-- The recursive retained-chunk value agrees with the flat semantic cell
sum used by the geometry bridge. -/
theorem retainedSuffixRectangleValue_eq_cells_sum
    (parameters : Parameters) (box : ProfileBox) (suffixChunks : List Chunk) :
    retainedSuffixRectangleValue parameters box suffixChunks =
      ((retainedSuffixCells box suffixChunks).map fun cell =>
        gaussianCellRectangleValue parameters box cell.1 cell.2).sum := by
  induction suffixChunks with
  | nil => simp [retainedSuffixRectangleValue, retainedSuffixCells]
  | cons chunk rest ih =>
      simp only [retainedSuffixRectangleValue]
      rw [boxRectangleChunkValue_eq_chunkCells_sum, ih]
      simp [retainedSuffixCells, List.sum_append]

/-- Executable elementary core obtained from the box's certified real-row
cap.  Its literal value is `cap^rows * T / λ`. -/
def constantCapCoreUpper (parameters : Parameters) (box : ProfileBox)
    (coreCutoff : ℚ) : UpperContourKernel.DInterval parameters.precision :=
  UpperContourKernel.frac parameters.precision (coreCutoff / box.lam) *
    UpperContourKernel.tensorPower
      (realCapUpper parameters.precision box.profileLeft box.lam)
      parameters.rowOddPart parameters.rowSquareCount

/-- The executable constant-cap core contains its elementary real value. -/
theorem constantCapCoreUpper_contains
    {parameters : Parameters} {box : ProfileBox} {coreCutoff : ℚ}
    {cap : ℝ}
    (hcap : (realCapUpper parameters.precision box.profileLeft box.lam).Contains
      cap) :
    (constantCapCoreUpper parameters box coreCutoff).Contains
      (cap ^ parameters.rows * (coreCutoff : ℝ) / (box.lam : ℝ)) := by
  have hcutoff := Interval.contains_ofRat parameters.precision
    (coreCutoff / box.lam)
  have hpower := UpperContourKernel.tensorPower_contains hcap
    parameters.rowOddPart parameters.rowSquareCount
  have hproduct := Interval.contains_mul hcutoff hpower
  have hvalue :
      cap ^ parameters.rows * (coreCutoff : ℝ) / (box.lam : ℝ) =
        ((coreCutoff / box.lam : ℚ) : ℝ) *
          cap ^ (parameters.rowOddPart * 2 ^ parameters.rowSquareCount) := by
    simp only [Parameters.rows]
    push_cast
    ring
  unfold constantCapCoreUpper
  rw [hvalue]
  simpa only [UpperContourKernel.frac] using hproduct

/-- A one-sided alternate integral endpoint: one analytic core, selected
suffix chunks, and the unchanged family tail from `boxIntegralFrom`. -/
def coreSubstitutedIntegral (parameters : Parameters) (box : ProfileBox)
    (coreUpper : UpperContourKernel.DInterval parameters.precision)
    (suffixChunks : List Chunk) :
    UpperContourKernel.DInterval parameters.precision :=
  let raw := boxIntegralFrom parameters box
    [coreUpper, retainedSuffixInterval parameters box suffixChunks]
  Interval.mk 0 raw.hi

/-- Security-scaled endpoint associated with `coreSubstitutedIntegral`. -/
def coreSubstitutedBound (parameters : Parameters) (box : ProfileBox)
    (coreUpper : UpperContourKernel.DInterval parameters.precision)
    (suffixChunks : List Chunk) :
    UpperContourKernel.DInterval parameters.precision :=
  boxPrefactor parameters box *
    coreSubstitutedIntegral parameters box coreUpper suffixChunks

/-- The numerical certificate boundary for one analytic-core substitution. -/
def CoreSubstitutedBudget (parameters : Parameters) (box : ProfileBox)
    (coreUpper : UpperContourKernel.DInterval parameters.precision)
    (suffixChunks : List Chunk) : Prop :=
  Interval.upperLTCheck
    (coreSubstitutedBound parameters box coreUpper suffixChunks) box.target = true

/-- Semantic endpoint used by alternative providers without changing the box's
public target. -/
def CoreSubstitutedBoxSound (parameters : Parameters) (box : ProfileBox) : Prop :=
  ∀ (d : ℕ) (a : Fin d → ℝ),
    ∑ i, a i ^ 2 = 1 →
    sparseProfileFourthMoment a ∈
      Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
    scaledUpperTailProbability parameters a < (box.target : ℝ)

/-- Retained executable chunks contain their literal rectangle sum. -/
theorem retainedSuffixInterval_contains
    {parameters : Parameters} {box : ProfileBox} {suffixChunks : List Chunk}
    (hchunk : ∀ chunk ∈ suffixChunks,
      (boxChunkValue parameters box chunk).Contains
        (boxRectangleChunkValue parameters box chunk)) :
    (retainedSuffixInterval parameters box suffixChunks).Contains
      (retainedSuffixRectangleValue parameters box suffixChunks) := by
  induction suffixChunks with
  | nil =>
      simpa [retainedSuffixInterval, retainedSuffixRectangleValue,
        UpperContourKernel.zero, UpperContourKernel.frac] using
        Interval.contains_ofRat parameters.precision (0 : ℚ)
  | cons chunk rest ih =>
      simp only [retainedSuffixInterval, retainedSuffixRectangleValue]
      apply Interval.contains_add
      · exact hchunk chunk (by simp)
      · apply ih
        intro other hother
        exact hchunk other (by simp [hother])

/-- A positive consecutive cell chain runs from its left endpoint no farther
than its right endpoint. -/
theorem cellChain_left_le_right
    {left right : ℚ} {cells : List (Segment × ℕ)}
    (hchain : CellChain left cells right) : left ≤ right := by
  induction cells generalizing left with
  | nil =>
      simpa [CellChain] using hchain.le
  | cons cell rest ih =>
      rcases hchain with ⟨hmesh, hcellLeft, hrest⟩
      have hleftCellRight : left ≤ cell.1.cellRight cell.2 := by
        rw [← hcellLeft]
        simp only [Segment.cellRight]
        exact le_add_of_nonneg_right hmesh.le
      exact hleftCellRight.trans (ih hrest)

/-- Consecutive positive semantic cells bound their exact union by the sum of
their Gaussian rectangles.  This is independent of segment boundaries. -/
theorem integral_Ioc_actualBoxQuadratureIntegrand_le_cellChain
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    {left right : ℚ} {cells : List (Segment × ℕ)}
    (hleft : 0 ≤ left)
    (hchain : CellChain left cells right)
    (hrow : ∀ cell ∈ cells, ∀ frequency ∈
      Ioc ((cell.1.cellLeft cell.2 : ℚ) : ℝ)
        ((cell.1.cellRight cell.2 : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box cell.1 cell.2) :
    (∫ frequency : ℝ in Ioc (left : ℝ) (right : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
      (cells.map fun cell =>
        gaussianCellRectangleValue parameters box cell.1 cell.2).sum := by
  have hintegrable := integrable_actualBoxQuadratureIntegrand facts hprofile
  induction cells generalizing left with
  | nil =>
      simp only [CellChain] at hchain
      subst right
      simp
  | cons cell rest ih =>
      rcases hchain with ⟨hmesh, hcellLeft, hrestChain⟩
      have hmeshReal : 0 < (cell.1.mesh : ℝ) := by exact_mod_cast hmesh
      have hcellLeftReal : ((cell.1.cellLeft cell.2 : ℚ) : ℝ) = (left : ℝ) := by
        exact_mod_cast hcellLeft
      have hcellLeftNonneg : 0 ≤ cell.1.cellLeft cell.2 := by
        rw [hcellLeft]
        exact hleft
      have hleftCellRight : (left : ℝ) ≤
          ((cell.1.cellRight cell.2 : ℚ) : ℝ) := by
        rw [← hcellLeftReal]
        exact_mod_cast (show cell.1.cellLeft cell.2 ≤
          cell.1.cellRight cell.2 by
            simp only [Segment.cellRight]
            exact le_add_of_nonneg_right hmesh.le)
      have hcellPointwise : ∀ frequency ∈
          Ioc (left : ℝ) ((cell.1.cellRight cell.2 : ℚ) : ℝ),
          actualBoxQuadratureIntegrand parameters box profile frequency ≤
            gaussianCellRectangleValue parameters box cell.1 cell.2 /
              (cell.1.mesh : ℝ) := by
        intro frequency hfrequency
        apply (le_div_iff₀ hmeshReal).2
        simpa only [mul_comm] using
          actualBoxQuadratureIntegrand_le_rectangle facts hprofile hmesh.le
            hcellLeftNonneg (by simpa only [hcellLeftReal] using hfrequency.1.le)
            (hrow cell (by simp) frequency (by
              simpa only [hcellLeftReal] using hfrequency))
      have hcellIntegral :
          (∫ frequency : ℝ in
            Ioc (left : ℝ) ((cell.1.cellRight cell.2 : ℚ) : ℝ),
            actualBoxQuadratureIntegrand parameters box profile frequency) ≤
              gaussianCellRectangleValue parameters box cell.1 cell.2 := by
        calc
          _ ≤ (((cell.1.cellRight cell.2 : ℚ) : ℝ) - (left : ℝ)) *
              (gaussianCellRectangleValue parameters box cell.1 cell.2 /
                (cell.1.mesh : ℝ)) :=
            _root_.CertifiedJL.integral_Ioc_le_length_mul hleftCellRight
              hintegrable.integrableOn hcellPointwise
          _ = gaussianCellRectangleValue parameters box cell.1 cell.2 := by
            rw [← hcellLeftReal]
            simp only [Segment.cellRight]
            push_cast
            field_simp
            ring
      have hcellRightNonneg : 0 ≤ cell.1.cellRight cell.2 :=
        hcellLeftNonneg.trans (by
          simp only [Segment.cellRight]
          exact le_add_of_nonneg_right hmesh.le)
      have hrestIntegral := ih hcellRightNonneg hrestChain
        (fun other hother frequency hfrequency =>
          hrow other (by simp [hother]) frequency hfrequency)
      have hcellRightEnd : ((cell.1.cellRight cell.2 : ℚ) : ℝ) ≤
          (right : ℝ) := by
        exact_mod_cast cellChain_left_le_right hrestChain
      have hdisjoint : Disjoint
          (Ioc (left : ℝ) ((cell.1.cellRight cell.2 : ℚ) : ℝ))
          (Ioc ((cell.1.cellRight cell.2 : ℚ) : ℝ) (right : ℝ)) :=
        Set.disjoint_left.2 fun _ hfirst hsecond =>
          (not_lt_of_ge hfirst.2) hsecond.1
      have hunion :
          Ioc (left : ℝ) ((cell.1.cellRight cell.2 : ℚ) : ℝ) ∪
              Ioc ((cell.1.cellRight cell.2 : ℚ) : ℝ) (right : ℝ) =
            Ioc (left : ℝ) (right : ℝ) := by
        ext frequency
        simp only [Set.mem_union, Set.mem_Ioc]
        constructor
        · rintro (hfrequency | hfrequency)
          · exact ⟨hfrequency.1, hfrequency.2.trans hcellRightEnd⟩
          · exact ⟨lt_of_le_of_lt hleftCellRight hfrequency.1, hfrequency.2⟩
        · intro hfrequency
          by_cases hfrequencyRight : frequency ≤
              ((cell.1.cellRight cell.2 : ℚ) : ℝ)
          · exact Or.inl ⟨hfrequency.1, hfrequencyRight⟩
          · exact Or.inr ⟨lt_of_not_ge hfrequencyRight, hfrequency.2⟩
      rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioc
        hintegrable.integrableOn hintegrable.integrableOn]
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add hcellIntegral hrestIntegral

/-- The exact suffix-geometry check and ordinary per-cell row bounds produce
the finite suffix premise needed by analytic-core substitution. -/
theorem integral_Ioc_actualBoxQuadratureIntegrand_le_retainedSuffix
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    {coreCutoff : ℚ} (hcoreCutoff : 0 ≤ coreCutoff)
    {suffixChunks : List Chunk}
    (hgeometry : retainedSuffixGeometryCheck box coreCutoff suffixChunks = true)
    (hrow : ∀ cell ∈ retainedSuffixCells box suffixChunks, ∀ frequency ∈
      Ioc ((cell.1.cellLeft cell.2 : ℚ) : ℝ)
        ((cell.1.cellRight cell.2 : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box cell.1 cell.2) :
    (∫ frequency : ℝ in Ioc (coreCutoff : ℝ) (box.cutoff : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        retainedSuffixRectangleValue parameters box suffixChunks := by
  rw [retainedSuffixRectangleValue_eq_cells_sum]
  exact integral_Ioc_actualBoxQuadratureIntegrand_le_cellChain facts hprofile
    hcoreCutoff (retainedSuffixGeometryCheck_sound hgeometry) hrow

/-- Split the complete positive-frequency integral into an analytic core, a
retained finite suffix, and the unchanged family tail. -/
theorem integral_Ioi_zero_actualBoxQuadratureIntegrand_le_core_suffix_tail
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    {coreCutoff : ℚ} (hcoreCutoff : 0 ≤ coreCutoff)
    (hcoreBeforeBoxCutoff : coreCutoff ≤ box.cutoff)
    (hboxCutoff : 0 < box.cutoff)
    {coreValue suffixValue : ℝ}
    (hcore :
      (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ),
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤
          coreValue)
    (hsuffix :
      (∫ frequency : ℝ in Ioc (coreCutoff : ℝ) (box.cutoff : ℝ),
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤
          suffixValue) :
    (∫ frequency : ℝ in Ioi 0,
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        coreValue + suffixValue + boxTailValue parameters box profile := by
  have hintegrable := integrable_actualBoxQuadratureIntegrand facts hprofile
  have htail := integral_Ioi_actualBoxQuadratureIntegrand_le_boxTailValue
    facts hprofile hboxCutoff
  have hboxCutoffReal : 0 < (box.cutoff : ℝ) := by
    exact_mod_cast hboxCutoff
  have hcoreSuffix : Disjoint
      (Ioc (0 : ℝ) (coreCutoff : ℝ))
      (Ioc (coreCutoff : ℝ) (box.cutoff : ℝ)) :=
    Set.disjoint_left.2 fun _ hleft hright =>
      (not_lt_of_ge hleft.2) hright.1
  have hunionCoreSuffix :
      Ioc (0 : ℝ) (coreCutoff : ℝ) ∪
          Ioc (coreCutoff : ℝ) (box.cutoff : ℝ) =
        Ioc 0 (box.cutoff : ℝ) := by
    ext frequency
    simp only [Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro (hfrequency | hfrequency)
      · exact ⟨hfrequency.1, hfrequency.2.trans (by exact_mod_cast hcoreBeforeBoxCutoff)⟩
      · exact ⟨lt_of_le_of_lt (by exact_mod_cast hcoreCutoff) hfrequency.1,
          hfrequency.2⟩
    · intro hfrequency
      by_cases hfrequencyCore : frequency ≤ (coreCutoff : ℝ)
      · exact Or.inl ⟨hfrequency.1, hfrequencyCore⟩
      · exact Or.inr ⟨lt_of_not_ge hfrequencyCore, hfrequency.2⟩
  have hfinite :
      (∫ frequency : ℝ in Ioc 0 (box.cutoff : ℝ),
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤
          coreValue + suffixValue := by
    rw [← hunionCoreSuffix, setIntegral_union hcoreSuffix measurableSet_Ioc
      hintegrable.integrableOn hintegrable.integrableOn]
    exact add_le_add hcore hsuffix
  have hfiniteTail : Disjoint
      (Ioc (0 : ℝ) (box.cutoff : ℝ)) (Ioi (box.cutoff : ℝ)) :=
    Set.disjoint_left.2 fun _ hleft hright =>
      (not_lt_of_ge hleft.2) hright
  have hunionFiniteTail :
      Ioc (0 : ℝ) (box.cutoff : ℝ) ∪ Ioi (box.cutoff : ℝ) = Ioi 0 := by
    ext frequency
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hfrequency | hfrequency)
      · exact hfrequency.1
      · exact hboxCutoffReal.trans hfrequency
    · intro hfrequency
      by_cases hfrequencyCutoff : frequency ≤ (box.cutoff : ℝ)
      · exact Or.inl ⟨hfrequency, hfrequencyCutoff⟩
      · exact Or.inr (lt_of_not_ge hfrequencyCutoff)
  rw [← hunionFiniteTail, setIntegral_union hfiniteTail measurableSet_Ioi
    hintegrable.integrableOn hintegrable.integrableOn]
  exact add_le_add hfinite htail

/-- The alternate executable integral contains the actual contour integral
once the analytic core and aligned retained suffix are proved sound. -/
theorem coreSubstitutedIntegral_contains
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    {coreCutoff : ℚ} (hcoreCutoff : 0 ≤ coreCutoff)
    (hcoreBeforeBoxCutoff : coreCutoff ≤ box.cutoff)
    (hboxCutoff : 0 < box.cutoff)
    {coreUpper : UpperContourKernel.DInterval parameters.precision}
    {suffixChunks : List Chunk} {coreValue : ℝ}
    (hcoreUpper : coreUpper.Contains coreValue)
    (hcore :
      (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ),
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤
          coreValue)
    (hsuffix :
      (∫ frequency : ℝ in Ioc (coreCutoff : ℝ) (box.cutoff : ℝ),
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤
          retainedSuffixRectangleValue parameters box suffixChunks)
    (hchunk : ∀ chunk ∈ suffixChunks,
      (boxChunkValue parameters box chunk).Contains
        (boxRectangleChunkValue parameters box chunk))
    (hcap : (realCapUpper parameters.precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    (coreSubstitutedIntegral parameters box coreUpper suffixChunks).Contains
      (∫ frequency : ℝ in Ioi 0,
        actualBoxQuadratureIntegrand parameters box profile frequency) := by
  let integralValue := ∫ frequency : ℝ in Ioi 0,
    actualBoxQuadratureIntegrand parameters box profile frequency
  let suffixValue := retainedSuffixRectangleValue parameters box suffixChunks
  let tailValue := boxTailValue parameters box profile
  have hsuffixContains := retainedSuffixInterval_contains hchunk
  have htailContains := boxTail_contains (parameters := parameters)
    (box := box) hcap
  have hzero : (UpperContourKernel.zero parameters.precision).Contains (0 : ℝ) := by
    simpa [UpperContourKernel.zero, UpperContourKernel.frac] using
      Interval.contains_ofRat parameters.precision (0 : ℚ)
  have hraw :
      (boxIntegralFrom parameters box
        [coreUpper, retainedSuffixInterval parameters box suffixChunks]).Contains
          (coreValue + suffixValue + tailValue) := by
    have hcells := Interval.contains_add
      (Interval.contains_add hzero hcoreUpper) hsuffixContains
    have hwhole := Interval.contains_add hcells htailContains
    simpa [boxIntegralFrom, suffixValue, tailValue,
      UpperContourKernel.zero, add_assoc] using hwhole
  have hintegralLe : integralValue ≤ coreValue + suffixValue + tailValue := by
    exact integral_Ioi_zero_actualBoxQuadratureIntegrand_le_core_suffix_tail
      facts hprofile hcoreCutoff hcoreBeforeBoxCutoff hboxCutoff hcore hsuffix
  have hintegralNonneg : 0 ≤ integralValue := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    exact actualBoxQuadratureIntegrand_nonneg facts hprofile frequency
  constructor
  · simpa [coreSubstitutedIntegral, integralValue] using hintegralNonneg
  · exact hintegralLe.trans (by
      simpa [coreSubstitutedIntegral, integralValue] using hraw.2)

/-- A core-substituted integral and a separate strict numerical budget prove
the unchanged rational box target. -/
theorem coreSubstitutedBoxSound_of_budget
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {coreCutoff : ℚ} (hcoreCutoff : 0 ≤ coreCutoff)
    (hcoreBeforeBoxCutoff : coreCutoff ≤ box.cutoff)
    (hboxCutoff : 0 < box.cutoff)
    {coreUpper : UpperContourKernel.DInterval parameters.precision}
    {suffixChunks : List Chunk}
    (budget : CoreSubstitutedBudget parameters box coreUpper suffixChunks)
    (hcoreUpper : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      ∃ coreValue : ℝ, coreUpper.Contains coreValue ∧
        (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ),
          actualBoxQuadratureIntegrand parameters box profile frequency) ≤ coreValue)
    (hsuffix : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (∫ frequency : ℝ in Ioc (coreCutoff : ℝ) (box.cutoff : ℝ),
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤
          retainedSuffixRectangleValue parameters box suffixChunks)
    (hchunk : ∀ chunk ∈ suffixChunks,
      (boxChunkValue parameters box chunk).Contains
        (boxRectangleChunkValue parameters box chunk))
    (hcap : ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper parameters.precision box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    CoreSubstitutedBoxSound parameters box := by
  intro d a hnorm hprofile
  let profile := sparseProfileFourthMoment a
  have hprofileNonneg : 0 ≤ profile := by
    have hleft : (0 : ℝ) ≤ box.profileLeft := by
      exact_mod_cast facts.profileLeft_nonneg
    exact hleft.trans hprofile.1
  obtain ⟨coreValue, hcoreContains, hcoreLe⟩ := hcoreUpper profile hprofile
  have hintegral := coreSubstitutedIntegral_contains facts hprofileNonneg
    hcoreCutoff hcoreBeforeBoxCutoff hboxCutoff hcoreContains hcoreLe
    (hsuffix profile hprofile) hchunk (hcap profile hprofile)
  have hprefactorContains := boxPrefactor_contains_rationalValue facts
  have hproduct := Interval.contains_mul hprefactorContains hintegral
  have hactualPrefactor := boxActualPrefactorValue_le_rationalValue facts
  have hintegralNonneg : 0 ≤ ∫ frequency : ℝ in Ioi 0,
      actualBoxQuadratureIntegrand parameters box profile frequency := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    exact actualBoxQuadratureIntegrand_nonneg facts hprofileNonneg frequency
  have hrationalNonneg : 0 ≤ boxRationalPrefactorValue parameters box := by
    have hlamDiff : (0 : ℚ) < 1 - box.lam := sub_pos.mpr facts.lam_lt_one
    have hphi : (0 : ℚ) < UpperContourKernel.phiLower box.theta := facts.phi_pos
    unfold boxRationalPrefactorValue
    dsimp only
    positivity
  have hscaled := scaledUpperTailProbability_le_actualBoxEndpoint
    facts a hnorm hprofile
  have hprefactorProduct :
      boxActualPrefactorValue parameters box *
          (∫ frequency : ℝ in Ioi 0,
            actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        boxRationalPrefactorValue parameters box *
          (∫ frequency : ℝ in Ioi 0,
            actualBoxQuadratureIntegrand parameters box profile frequency) :=
    mul_le_mul_of_nonneg_right hactualPrefactor hintegralNonneg
  have hupper :
      boxRationalPrefactorValue parameters box *
          (∫ frequency : ℝ in Ioi 0,
            actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        ((coreSubstitutedBound parameters box coreUpper suffixChunks).upperRat : ℝ) := by
    simpa [coreSubstitutedBound, Interval.upperRat, Dyadic.cast_toRat] using hproduct.2
  have hbudgetRat :
      (coreSubstitutedBound parameters box coreUpper suffixChunks).upperRat <
        box.target := Interval.upperLTCheck_sound budget
  have hbudgetReal :
      ((coreSubstitutedBound parameters box coreUpper suffixChunks).upperRat : ℝ) <
        (box.target : ℝ) := by exact_mod_cast hbudgetRat
  exact hscaled.trans (hprefactorProduct.trans hupper) |>.trans_lt hbudgetReal

/-! ## Reusable analytic core bounds -/

/-- A uniform row cap bounds the literal contour integrand by `cap^rows / λ`.
The shifted Gaussian is discarded here; this cheap bound is useful near zero
and for boxes whose real-row cap is already small. -/
theorem actualBoxQuadratureIntegrand_le_constantCap
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile cap frequency : ℝ} (hprofile : 0 ≤ profile)
    (hcapNonneg : 0 ≤ cap)
    (hrow : sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤ cap) :
    actualBoxQuadratureIntegrand parameters box profile frequency ≤
      cap ^ parameters.rows / (box.lam : ℝ) := by
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast facts.lam_pos
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast facts.lam_lt_one
  have hrowNonneg := SparseUpperContour.sparseUpperContourRowMajorant_nonneg
    (frequency := frequency) hprofile hlam.le hlamOne
  have hrowPower := pow_le_pow_left₀ hrowNonneg hrow parameters.rows
  have hcapPowerNonneg : 0 ≤ cap ^ parameters.rows :=
    pow_nonneg hcapNonneg parameters.rows
  have hgaussian :
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by norm_num))) (sq_nonneg _)
  have hsqrt : (box.lam : ℝ) ≤
      Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) :=
    (Real.le_sqrt hlam.le (by positivity)).2 (by nlinarith [sq_nonneg frequency])
  have hinverse :
      1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) ≤
        1 / (box.lam : ℝ) :=
    one_div_le_one_div_of_le hlam hsqrt
  have hinverseNonneg :
      0 ≤ 1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) := by
    positivity
  unfold actualBoxQuadratureIntegrand
  calc
    _ ≤ 1 * cap ^ parameters.rows *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hgaussian hrowPower
          (pow_nonneg hrowNonneg parameters.rows) (by norm_num))
        hinverseNonneg
    _ ≤ 1 * cap ^ parameters.rows * (1 / (box.lam : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hinverse (by positivity)
    _ = cap ^ parameters.rows / (box.lam : ℝ) := by ring

/-- Integrating a uniform row cap over `(0,T]` gives the elementary
`cap^rows * T / λ` core bound. -/
theorem integral_Ioc_actualBoxQuadratureIntegrand_le_constantCap
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile cap : ℝ} (hprofile : 0 ≤ profile)
    (hcapNonneg : 0 ≤ cap) {coreCutoff : ℚ}
    (hcoreCutoff : 0 ≤ coreCutoff)
    (hrow : ∀ frequency ∈ Icc (0 : ℝ) (coreCutoff : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤ cap) :
    (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        cap ^ parameters.rows * (coreCutoff : ℝ) / (box.lam : ℝ) := by
  have hpointwise : ∀ frequency ∈ Ioc (0 : ℝ) (coreCutoff : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency ≤
        cap ^ parameters.rows / (box.lam : ℝ) := by
    intro frequency hfrequency
    exact actualBoxQuadratureIntegrand_le_constantCap facts hprofile hcapNonneg
      (hrow frequency ⟨hfrequency.1.le, hfrequency.2⟩)
  have hintegrable : IntegrableOn
      (actualBoxQuadratureIntegrand parameters box profile)
      (Ioc (0 : ℝ) (coreCutoff : ℝ)) :=
    (integrable_actualBoxQuadratureIntegrand facts hprofile).integrableOn
  calc
    _ ≤ ((coreCutoff : ℝ) - 0) *
        (cap ^ parameters.rows / (box.lam : ℝ)) :=
      _root_.CertifiedJL.integral_Ioc_le_length_mul
        (by exact_mod_cast hcoreCutoff) hintegrable hpointwise
    _ = cap ^ parameters.rows * (coreCutoff : ℝ) / (box.lam : ℝ) := by ring

/-- Exact positive-half-line Gaussian integral. -/
theorem integral_Ioi_exp_neg_mul_sq_eq_halfGaussian
    {rate : ℝ} (hrate : 0 < rate) :
    (∫ frequency : ℝ in Ioi 0, Real.exp (-rate * frequency ^ 2)) =
      Real.sqrt (Real.pi / rate) / 2 := by
  let envelope : ℝ → ℝ := fun frequency => Real.exp (-rate * frequency ^ 2)
  have hintegrable : Integrable envelope := by
    simpa only [envelope] using integrable_exp_neg_mul_sq hrate
  have heven (frequency : ℝ) : envelope (-frequency) = envelope frequency := by
    simp only [envelope, neg_sq]
  have hleft :
      (∫ frequency : ℝ in Iic 0, envelope frequency) =
        ∫ frequency : ℝ in Ioi 0, envelope frequency := by
    calc
      (∫ frequency : ℝ in Iic 0, envelope frequency) =
          ∫ frequency : ℝ in Iic 0, envelope (-frequency) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro frequency _
        exact (heven frequency).symm
      _ = ∫ frequency : ℝ in Ioi 0, envelope frequency := by simp
  have hsplit := integral_add_compl (μ := volume) (s := Ioi (0 : ℝ))
    measurableSet_Ioi hintegrable
  rw [compl_Ioi, hleft] at hsplit
  have hfull : (∫ frequency : ℝ, envelope frequency) =
      Real.sqrt (Real.pi / rate) := by
    simpa only [envelope] using integral_gaussian rate
  rw [hfull] at hsplit
  linarith

/-- A Gaussian row envelope propagates through all rows, the contour Gaussian,
and the radial factor. -/
theorem actualBoxQuadratureIntegrand_le_gaussianOfRowEnvelope
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile K kappa frequency : ℝ} (hprofile : 0 ≤ profile)
    (hK : 0 ≤ K)
    (hrow : sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      K * Real.exp (-kappa * frequency ^ 2)) :
    actualBoxQuadratureIntegrand parameters box profile frequency ≤
      (K ^ parameters.rows / (box.lam : ℝ)) *
        Real.exp (-(((parameters.rows : ℝ) * kappa +
          (box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2)) := by
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast facts.lam_pos
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast facts.lam_lt_one
  have hrowNonneg := SparseUpperContour.sparseUpperContourRowMajorant_nonneg
    (frequency := frequency) hprofile hlam.le hlamOne
  have henvelopeNonneg : 0 ≤ K * Real.exp (-kappa * frequency ^ 2) := by
    positivity
  have hrowPower := pow_le_pow_left₀ hrowNonneg hrow parameters.rows
  have hsqrt : (box.lam : ℝ) ≤
      Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) :=
    (Real.le_sqrt hlam.le (by positivity)).2 (by nlinarith [sq_nonneg frequency])
  have hinverse :
      1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) ≤
        1 / (box.lam : ℝ) :=
    one_div_le_one_div_of_le hlam hsqrt
  have hleftNonneg : 0 ≤
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
        sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^
          parameters.rows := by positivity
  unfold actualBoxQuadratureIntegrand
  calc
    _ ≤ Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (K * Real.exp (-kappa * frequency ^ 2)) ^ parameters.rows *
          (1 / (box.lam : ℝ)) := by
      gcongr
    _ = (K ^ parameters.rows / (box.lam : ℝ)) *
        Real.exp (-(((parameters.rows : ℝ) * kappa +
          (box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      calc
        Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
              (K ^ parameters.rows *
                Real.exp ((parameters.rows : ℝ) *
                  (-kappa * frequency ^ 2))) *
              (1 / (box.lam : ℝ)) =
            (K ^ parameters.rows / (box.lam : ℝ)) *
              (Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
                Real.exp ((parameters.rows : ℝ) *
                  (-kappa * frequency ^ 2))) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring

/-- A Gaussian row envelope on `(0,T]` is dominated by its complete
half-Gaussian integral. -/
theorem integral_Ioc_actualBoxQuadratureIntegrand_le_halfGaussian
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile K kappa : ℝ} (hprofile : 0 ≤ profile) (hK : 0 ≤ K)
    {coreCutoff : ℚ}
    (hrate : 0 < (parameters.rows : ℝ) * kappa +
      (box.sigma : ℝ) ^ 2 / 2)
    (hrow : ∀ frequency ∈ Icc (0 : ℝ) (coreCutoff : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        K * Real.exp (-kappa * frequency ^ 2)) :
    (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        (K ^ parameters.rows / (box.lam : ℝ)) *
          (Real.sqrt (Real.pi /
            ((parameters.rows : ℝ) * kappa + (box.sigma : ℝ) ^ 2 / 2)) / 2) := by
  let rate := (parameters.rows : ℝ) * kappa + (box.sigma : ℝ) ^ 2 / 2
  let envelope : ℝ → ℝ := fun frequency =>
    (K ^ parameters.rows / (box.lam : ℝ)) *
      Real.exp (-rate * frequency ^ 2)
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast facts.lam_pos
  have hcoefficientNonneg : 0 ≤ K ^ parameters.rows / (box.lam : ℝ) := by
    positivity
  have henvelope : Integrable envelope :=
    (integrable_exp_neg_mul_sq (by simpa only [rate] using hrate)).const_mul _
  have hcore :
      (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ),
        actualBoxQuadratureIntegrand parameters box profile frequency) ≤
      ∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ), envelope frequency := by
    apply setIntegral_mono_on
    · exact (integrable_actualBoxQuadratureIntegrand facts hprofile).integrableOn
    · exact henvelope.integrableOn
    · exact measurableSet_Ioc
    · intro frequency hfrequency
      calc
        _ ≤ (K ^ parameters.rows / (box.lam : ℝ)) *
            Real.exp (-(((parameters.rows : ℝ) * kappa +
              (box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2)) :=
          actualBoxQuadratureIntegrand_le_gaussianOfRowEnvelope
            facts hprofile hK (hrow frequency ⟨hfrequency.1.le, hfrequency.2⟩)
        _ = envelope frequency := by
          dsimp only [envelope, rate]
          congr 2
          ring
  have hset :
      (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ), envelope frequency) ≤
        ∫ frequency : ℝ in Ioi 0, envelope frequency := by
    apply setIntegral_mono_set henvelope.integrableOn
    · exact ae_of_all _ fun frequency => by
        dsimp only [envelope]
        positivity
    · exact ae_of_all _ fun _ hfrequency => hfrequency.1
  calc
    _ ≤ ∫ frequency : ℝ in Ioi 0, envelope frequency := hcore.trans hset
    _ = (K ^ parameters.rows / (box.lam : ℝ)) *
        (Real.sqrt (Real.pi / rate) / 2) := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_exp_neg_mul_sq_eq_halfGaussian
          (by simpa only [rate] using hrate)]
    _ = _ := by rfl

/-- Convenience form matching signed-core certificates stated as
`row ≤ exp (-δ - κ u²)`. -/
theorem integral_Ioc_actualBoxQuadratureIntegrand_le_halfGaussianOfExpEnvelope
    {parameters : Parameters} {box : ProfileBox}
    (facts : LowProfileFacts parameters box)
    {profile delta kappa : ℝ} (hprofile : 0 ≤ profile)
    {coreCutoff : ℚ}
    (hrate : 0 < (parameters.rows : ℝ) * kappa +
      (box.sigma : ℝ) ^ 2 / 2)
    (hrow : ∀ frequency ∈ Icc (0 : ℝ) (coreCutoff : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        Real.exp (-delta - kappa * frequency ^ 2)) :
    (∫ frequency : ℝ in Ioc 0 (coreCutoff : ℝ),
      actualBoxQuadratureIntegrand parameters box profile frequency) ≤
        (Real.exp (-delta) ^ parameters.rows / (box.lam : ℝ)) *
          (Real.sqrt (Real.pi /
            ((parameters.rows : ℝ) * kappa + (box.sigma : ℝ) ^ 2 / 2)) / 2) := by
  apply integral_Ioc_actualBoxQuadratureIntegrand_le_halfGaussian
    facts hprofile (Real.exp_nonneg _) hrate
  intro frequency hfrequency
  calc
    _ ≤ Real.exp (-delta - kappa * frequency ^ 2) :=
      hrow frequency hfrequency
    _ = Real.exp (-delta) * Real.exp (-kappa * frequency ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

end CertifiedJL.SparseUpperContourFamily
