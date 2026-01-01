/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ConcreteSoundness

/-!
# Arithmetic aggregation for the sparse upper hybrid certificate

This file connects the semantic rectangle sums to the same left-associated
interval chunks that the generated kernel replay checks.
-/

namespace CertifiedJL
namespace SparseUpperHybrid

open UpperContourKernel

private theorem upperRat_zero :
    (((zero precision).upperRat : ℚ) : ℝ) = 0 := by
  norm_num [zero, frac, Interval.upperRat, Interval.ofRat, Interval.enclose,
    Dyadic.roundUp, Dyadic.toRat]

private theorem upperRat_add (I J : DInterval precision) :
    (((I + J).upperRat : ℚ) : ℝ) =
      (I.upperRat : ℝ) + (J.upperRat : ℝ) := by
  change (Dyadic.toRat precision (I.hi + J.hi) : ℝ) =
    (Dyadic.toRat precision I.hi : ℝ) +
      (Dyadic.toRat precision J.hi : ℝ)
  rw [Dyadic.toRat_add]
  norm_num

/-- A checked consecutive block of cells bounds the corresponding semantic
rectangle block. -/
theorem sum_rectangles_le_segmentChunk_upperRat
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    {profile : ℝ}
    (hprofile : profile ∈ Set.Icc (certificate.box.profileLeft : ℝ)
      (certificate.box.profileRight : ℝ))
    (segment : Segment) (hsegment : segment ∈ certificate.segments)
    (start count : ℕ)
    (hcount : start + count ≤ segment.count)
    (hchecks : ∀ i < segment.count,
      hybridCellSideCheck certificate.box segment i = true) :
    (∑ offset ∈ Finset.range count,
        hybridCellRectangleValue certificate.box segment (start + offset)) ≤
      ((segmentChunk certificate.box segment start count).upperRat : ℝ) := by
  induction count with
  | zero => simpa [segmentChunk, upperRat_zero]
  | succ count ih =>
      have hprev : start + count ≤ segment.count :=
        le_trans (Nat.le_succ _) hcount
      have hindex : start + count < segment.count := by omega
      rw [Finset.sum_range_succ]
      rw [segmentChunk, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [upperRat_add]
      exact add_le_add (ih hprev)
        (certificateBox_hybridCellRectangle_le_upperRat hcertificate hprofile
          segment hsegment (start + count) (hchecks _ hindex))

/-! ## Structural coverage of the ten-cell chunk plan -/

/-- A cell reference is a segment index together with an index inside that
segment.  Keeping coverage at this purely natural-number level prevents the
aggregation proof from evaluating any interval cells. -/
private abbrev CellRef := ℕ × ℕ

private def chunkCellRefs (chunk : Chunk) : List CellRef :=
  (List.range chunk.count).map fun offset =>
    (chunk.segmentIndex, chunk.start + offset)

private def planCellRefs (plan : List Chunk) : List CellRef :=
  plan.flatMap chunkCellRefs

private def certificateCellRefs (certificate : CertificateBox) : List CellRef :=
  certificate.segments.zipIdx.flatMap fun pair =>
    (List.range pair.1.count).map fun index => (pair.2, index)

/-- The inexpensive structural obligations for a chunk plan: every chunk
references an existing segment, stays inside it, and the flattened references
are exactly all certificate cells in segment order. -/
private def chunkPlanValidCheck (certificate : CertificateBox)
    (plan : List Chunk) : Bool :=
  (plan.all fun chunk => decide
    (chunk.segmentIndex < certificate.segments.length ∧
      chunk.start + chunk.count ≤
        (certificate.segments.getD chunk.segmentIndex default).count)) &&
  decide (planCellRefs plan = certificateCellRefs certificate)

private theorem foldl_add_eq_add_sum_map
    {A : Type*} (xs : List A) (f : A → ℝ) (x : ℝ) :
    xs.foldl (fun acc i => acc + f i) x = x + (xs.map f).sum := by
  induction xs generalizing x with
  | nil => simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring

private theorem finset_sum_range_eq_list_sum_map
    (n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, List.range_succ, ih]

private theorem sum_map_sum_eq_sum_flatMap
    {A B : Type*} (xs : List A) (g : A → List B) (f : B → ℝ) :
    (xs.map (fun x => ((g x).map f).sum)).sum =
      ((xs.flatMap g).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.sum_append]

private theorem finiteIntegralFrom_upperRat
    (chunks : List (DInterval precision)) :
    ((finiteIntegralFrom chunks).upperRat : ℝ) =
      (chunks.map fun chunk => (chunk.upperRat : ℝ)).sum := by
  have aux : ∀ (xs : List (DInterval precision)) (I : DInterval precision),
      ((xs.foldl (· + ·) I).upperRat : ℝ) =
        (I.upperRat : ℝ) +
          (xs.map fun chunk => (chunk.upperRat : ℝ)).sum := by
    intro xs
    induction xs with
    | nil => intro I; simp
    | cons chunk xs ih =>
        intro I
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih, upperRat_add]
        ring
  unfold finiteIntegralFrom
  rw [aux, upperRat_zero, zero_add]

private noncomputable def rectangleAt
    (certificate : CertificateBox) (cell : CellRef) : ℝ :=
  hybridCellRectangleValue certificate.box
    (certificate.segments.getD cell.1 default) cell.2

private noncomputable def chunkRectangleSum
    (certificate : CertificateBox) (chunk : Chunk) : ℝ :=
  ∑ offset ∈ Finset.range chunk.count,
    rectangleAt certificate (chunk.segmentIndex, chunk.start + offset)

private theorem chunkRectangleSum_eq_refs
    (certificate : CertificateBox) (chunk : Chunk) :
    chunkRectangleSum certificate chunk =
      ((chunkCellRefs chunk).map (rectangleAt certificate)).sum := by
  unfold chunkRectangleSum
  rw [finset_sum_range_eq_list_sum_map]
  simp only [chunkCellRefs, List.map_map, Function.comp_def]

private theorem planRectangleSum_eq_refs
    (certificate : CertificateBox) (plan : List Chunk) :
    (plan.map (chunkRectangleSum certificate)).sum =
      ((planCellRefs plan).map (rectangleAt certificate)).sum := by
  have h := sum_map_sum_eq_sum_flatMap plan chunkCellRefs
    (rectangleAt certificate)
  rw [planCellRefs]
  rw [← h]
  apply congrArg List.sum
  apply List.map_congr_left
  intro chunk _
  exact chunkRectangleSum_eq_refs certificate chunk

private theorem certificateRectangleSum_eq_refs
    (certificate : CertificateBox) :
    (certificate.segments.map
      (segmentRectangleSum certificate.box)).sum =
      ((certificateCellRefs certificate).map
        (rectangleAt certificate)).sum := by
  rw [← List.zipIdx_map_fst 0 certificate.segments]
  simp only [List.map_map, certificateCellRefs]
  let cellsForPair : Segment × ℕ → List CellRef := fun pair =>
    (List.range pair.1.count).map fun index => (pair.2, index)
  calc
    (certificate.segments.zipIdx.map
        (segmentRectangleSum certificate.box ∘ Prod.fst)).sum =
        (certificate.segments.zipIdx.map fun pair =>
          ((cellsForPair pair).map (rectangleAt certificate)).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro pair hpair
      change segmentRectangleSum certificate.box pair.1 = _
      unfold segmentRectangleSum
      rw [finset_sum_range_eq_list_sum_map]
      apply congrArg List.sum
      simp only [cellsForPair, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro index _
      rcases pair with ⟨segment, segmentIndex⟩
      have hpair' := List.mem_zipIdx hpair
      have hindex : segmentIndex < certificate.segments.length := by
        omega
      have hsegment :
          certificate.segments.getD segmentIndex default = segment := by
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hindex, hpair'.2.2]
      simp only [rectangleAt]
      rw [hsegment]
    _ = ((certificate.segments.zipIdx.flatMap cellsForPair).map
          (rectangleAt certificate)).sum :=
      sum_map_sum_eq_sum_flatMap certificate.segments.zipIdx cellsForPair
        (rectangleAt certificate)
    _ = ((certificate.segments.zipIdx.flatMap fun pair =>
          (List.range pair.1.count).map fun index => (pair.2, index)).map
          (rectangleAt certificate)).sum := by rfl

/-- Every manifest chunk plan is structurally valid.  This check only reduces
lists of natural-number references; it does not unfold `hybridCell`. -/
private theorem certificateChunkPlan_valid
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    chunkPlanValidCheck certificate (certificateChunkPlan certificate) = true := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- The sum of all five semantic rectangle partitions is bounded by the upper
endpoint of the exact interval sum replayed by the ten-cell chunk plan. -/
theorem certificate_rectangleSums_le_finiteIntegralFrom_upperRat
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    {profile : ℝ}
    (hprofile : profile ∈ Set.Icc (certificate.box.profileLeft : ℝ)
      (certificate.box.profileRight : ℝ))
    (hchecks : ∀ segment ∈ certificate.segments, ∀ i < segment.count,
      hybridCellSideCheck certificate.box segment i = true) :
    (certificate.segments.map
      (segmentRectangleSum certificate.box)).sum ≤
      ((finiteIntegralFrom
        ((certificateChunkPlan certificate).map
          (certificateChunkValue certificate))).upperRat : ℝ) := by
  have hvalid := certificateChunkPlan_valid hcertificate
  have hvalidParts :
      ((certificateChunkPlan certificate).all fun chunk => decide
        (chunk.segmentIndex < certificate.segments.length ∧
          chunk.start + chunk.count ≤
            (certificate.segments.getD chunk.segmentIndex default).count)) = true ∧
        decide (planCellRefs (certificateChunkPlan certificate) =
          certificateCellRefs certificate) = true := by
    simpa only [chunkPlanValidCheck, Bool.and_eq_true] using hvalid
  have hcoverage : planCellRefs (certificateChunkPlan certificate) =
      certificateCellRefs certificate :=
    of_decide_eq_true hvalidParts.2
  have hchunk : ∀ chunk ∈ certificateChunkPlan certificate,
      chunkRectangleSum certificate chunk ≤
        ((certificateChunkValue certificate chunk).upperRat : ℝ) := by
    intro chunk hchunk
    have hboundsBool := (List.all_eq_true.mp hvalidParts.1) chunk hchunk
    have hbounds :
        chunk.segmentIndex < certificate.segments.length ∧
          chunk.start + chunk.count ≤
            (certificate.segments.getD chunk.segmentIndex default).count :=
      of_decide_eq_true hboundsBool
    have hsegment :
        certificate.segments.getD chunk.segmentIndex default ∈
          certificate.segments := by
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hbounds.1]
    exact sum_rectangles_le_segmentChunk_upperRat hcertificate hprofile
      (certificate.segments.getD chunk.segmentIndex default) hsegment
      chunk.start chunk.count hbounds.2
      (hchecks _ hsegment)
  calc
    (certificate.segments.map
        (segmentRectangleSum certificate.box)).sum =
        (certificateChunkPlan certificate |>.map
          (chunkRectangleSum certificate)).sum := by
      rw [planRectangleSum_eq_refs, certificateRectangleSum_eq_refs,
        hcoverage]
    _ ≤ (certificateChunkPlan certificate |>.map fun chunk =>
          ((certificateChunkValue certificate chunk).upperRat : ℝ)).sum := by
      exact List.sum_le_sum hchunk
    _ = ((finiteIntegralFrom
          ((certificateChunkPlan certificate).map
            (certificateChunkValue certificate))).upperRat : ℝ) := by
      rw [finiteIntegralFrom_upperRat]
      simp only [List.map_map, Function.comp_def]

end SparseUpperHybrid
end CertifiedJL
