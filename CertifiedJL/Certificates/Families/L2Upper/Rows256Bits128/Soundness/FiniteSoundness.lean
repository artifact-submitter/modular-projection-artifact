/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Soundness

/-!
# Finite-part soundness for the centered-hybrid certificate

This file turns the pointwise rectangle theorem into a reusable integral
bound for an arbitrary rational frequency segment.  The numerical replay is
kept separate: callers only supply the row and compact-transform inequalities
on each cell.
-/

open MeasureTheory

namespace CertifiedJL
namespace SparseUpperHybrid

/-- The row-majorant hypotheses required by every cell of one segment. -/
def SegmentRowBounds (box : ProfileBox) (profile : ℝ)
    (segment : Segment) : Prop :=
  ∀ i < segment.count, ∀ frequency ∈
    Set.Ioc
      (((segment.start + i * segment.mesh : ℚ) : ℝ))
      (((segment.start + (i + 1) * segment.mesh : ℚ) : ℝ)),
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      hybridCellRowUpperValue box segment i

/-- The compact-transform hypotheses required by every cell of one segment. -/
def SegmentCompactBounds (box : ProfileBox) (segment : Segment) : Prop :=
  ∀ i < segment.count, ∀ frequency ∈
    Set.Ioc
      (((segment.start + i * segment.mesh : ℚ) : ℝ))
      (((segment.start + (i + 1) * segment.mesh : ℚ) : ℝ)),
    ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
        (box.lam : ℝ) frequency‖ ^ box.uniformCount ≤
      ((compactNoiseUpper box
        (segment.start + i * segment.mesh)).upperRat : ℝ)

/-- The literal rectangle sum attached to one segment. -/
noncomputable def segmentRectangleSum (box : ProfileBox)
    (segment : Segment) : ℝ :=
  ∑ i ∈ Finset.range segment.count,
    hybridCellRectangleValue box segment i

private theorem integral_Ioc_add
    {f : ℝ → ℝ} (hf : Integrable f) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x : ℝ in Set.Ioc a c, f x) =
      (∫ x : ℝ in Set.Ioc a b, f x) +
        ∫ x : ℝ in Set.Ioc b c, f x := by
  have hdisjoint : Disjoint (Set.Ioc a b) (Set.Ioc b c) := by
    exact Set.disjoint_left.2 fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  have hunion : Set.Ioc a b ∪ Set.Ioc b c = Set.Ioc a c := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans hbc⟩
      · exact ⟨lt_of_le_of_lt hab hx.1, hx.2⟩
    · intro hx
      by_cases hxb : x ≤ b
      · exact Or.inl ⟨hx.1, hxb⟩
      · exact Or.inr ⟨lt_of_not_ge hxb, hx.2⟩
  rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioc
    hf.integrableOn hf.integrableOn]

/-- The cells of one positive-mesh segment dominate the analytic integral on
the corresponding half-open interval. -/
theorem integral_Ioc_actualHybridIntegrand_le_sum_rectangles
    (box : ProfileBox) (segment : Segment) (profile : ℝ)
    (hprofile : 0 ≤ profile)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1)
    (hstart : 0 ≤ (segment.start : ℝ))
    (hmesh : 0 < (segment.mesh : ℝ))
    (hrow : ∀ i < segment.count, ∀ frequency ∈
      Set.Ioc
        (((segment.start + i * segment.mesh : ℚ) : ℝ))
        (((segment.start + (i + 1) * segment.mesh : ℚ) : ℝ)),
      sparseUpperContourRowMajorant
          profile (box.lam : ℝ) frequency ≤
        hybridCellRowUpperValue box segment i)
    (hcompact : ∀ i < segment.count, ∀ frequency ∈
      Set.Ioc
        (((segment.start + i * segment.mesh : ℚ) : ℝ))
        (((segment.start + (i + 1) * segment.mesh : ℚ) : ℝ)),
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ^ box.uniformCount ≤
        ((compactNoiseUpper box
          (segment.start + i * segment.mesh)).upperRat : ℝ)) :
    (∫ frequency : ℝ in Set.Ioc (segment.start : ℝ)
        ((segment.start + segment.count * segment.mesh : ℚ) : ℝ),
      actualHybridIntegrand box profile frequency) ≤
      ∑ i ∈ Finset.range segment.count,
        hybridCellRectangleValue box segment i := by
  have hint := integrable_actualHybridIntegrand box profile hprofile
    hh hlam hlamOne
  have hprefix : ∀ n ≤ segment.count,
      (∫ frequency : ℝ in Set.Ioc (segment.start : ℝ)
          ((segment.start + n * segment.mesh : ℚ) : ℝ),
        actualHybridIntegrand box profile frequency) ≤
        ∑ i ∈ Finset.range n,
          hybridCellRectangleValue box segment i := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hnPrevious : n ≤ segment.count := Nat.le_of_succ_le hn
      have hnCell : n < segment.count := Nat.lt_of_succ_le hn
      have hprevious := ih hnPrevious
      let left : ℝ := ((segment.start + n * segment.mesh : ℚ) : ℝ)
      let right : ℝ := ((segment.start + (n + 1) * segment.mesh : ℚ) : ℝ)
      let rectangle : ℝ := hybridCellRectangleValue box segment n
      have hleftNonneg : 0 ≤ left := by
        dsimp only [left]
        push_cast
        positivity
      have hleftRight : left ≤ right := by
        dsimp only [left, right]
        push_cast
        have hmesh' : (0 : ℝ) < segment.mesh := hmesh
        nlinarith
      have hcellPointwise : ∀ frequency ∈ Set.Ioc left right,
          actualHybridIntegrand box profile frequency ≤ rectangle / segment.mesh := by
        intro frequency hfrequency
        apply (le_div_iff₀ hmesh).2
        dsimp only [rectangle, left, right] at hfrequency ⊢
        simpa only [mul_comm] using
          actualHybridIntegrand_le_rectangle box segment n profile frequency
            hprofile hlam hlamOne hmesh.le hleftNonneg hfrequency.1.le
            (hrow n hnCell frequency hfrequency)
            (hcompact n hnCell frequency hfrequency)
      have hcell :
          (∫ frequency : ℝ in Set.Ioc left right,
            actualHybridIntegrand box profile frequency) ≤ rectangle := by
        calc
          _ ≤ ∫ _frequency : ℝ in Set.Ioc left right,
              rectangle / segment.mesh := by
            apply setIntegral_mono_on hint.integrableOn
              (integrableOn_const (hs := by
                rw [Real.volume_Ioc]
                exact ENNReal.ofReal_ne_top)) measurableSet_Ioc
            exact hcellPointwise
          _ = rectangle := by
            rw [setIntegral_const]
            simp only [smul_eq_mul, Measure.real, Real.volume_Ioc]
            rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hleftRight)]
            dsimp only [left, right]
            push_cast
            field_simp
            ring
      have hdisjoint : Disjoint
          (Set.Ioc (segment.start : ℝ) left) (Set.Ioc left right) := by
        exact Set.disjoint_left.2 fun x hx hy => (not_lt_of_ge hx.2) hy.1
      have hunion : Set.Ioc (segment.start : ℝ) left ∪ Set.Ioc left right =
          Set.Ioc (segment.start : ℝ) right := by
        have hstartLeft : (segment.start : ℝ) ≤ left := by
          dsimp only [left]
          push_cast
          exact le_add_of_nonneg_right (mul_nonneg (by positivity) hmesh.le)
        ext x
        simp only [Set.mem_union, Set.mem_Ioc]
        constructor
        · rintro (hx | hx)
          · exact ⟨hx.1, hx.2.trans hleftRight⟩
          · exact ⟨lt_of_le_of_lt hstartLeft hx.1, hx.2⟩
        · intro hx
          by_cases hxl : x ≤ left
          · exact Or.inl ⟨hx.1, hxl⟩
          · exact Or.inr ⟨lt_of_not_ge hxl, hx.2⟩
      have hgoal : (∫ frequency : ℝ in Set.Ioc (segment.start : ℝ) right,
          actualHybridIntegrand box profile frequency) ≤
          ∑ i ∈ Finset.range (n + 1),
            hybridCellRectangleValue box segment i := by
        rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioc
          hint.integrableOn hint.integrableOn]
        rw [Finset.sum_range_succ]
        simpa only using add_le_add hprevious hcell
      simpa only [right, Nat.cast_add, Nat.cast_one] using hgoal
  exact hprefix segment.count le_rfl

/-- The four positive-length manifest segments jointly dominate the finite
contour integral on `(0,8]`.  Segment meshes may differ, but each is
represented as the reciprocal of a positive natural denominator. -/
theorem integral_Ioc_zero_cutoff_le_mkSegments_rectangleSums
    (box : ProfileBox) (profile : ℝ) (d0 d1 d2 d3 d4 : ℕ)
    (hprofile : 0 ≤ profile)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hd3 : 0 < d3) (hd4 : 0 < d4)
    (hrow : ∀ segment ∈ mkSegments d0 d1 d2 d3 d4,
      SegmentRowBounds box profile segment)
    (hcompact : ∀ segment ∈ mkSegments d0 d1 d2 d3 d4,
      SegmentCompactBounds box segment) :
    (∫ frequency : ℝ in Set.Ioc 0 (cutoff : ℝ),
      actualHybridIntegrand box profile frequency) ≤
      ((mkSegments d0 d1 d2 d3 d4).map
        (segmentRectangleSum box)).sum := by
  let s0 : Segment := ⟨0, 1 / d0, d0⟩
  let s1 : Segment := ⟨1, 1 / d1, d1⟩
  let s2 : Segment := ⟨2, 1 / d2, 2 * d2⟩
  let s3 : Segment := ⟨4, 1 / d3, 4 * d3⟩
  let s4 : Segment := ⟨8, 1 / d4, 0⟩
  have hs0mem : s0 ∈ mkSegments d0 d1 d2 d3 d4 := by
    simp [s0, mkSegments]
  have hs1mem : s1 ∈ mkSegments d0 d1 d2 d3 d4 := by
    simp [s1, mkSegments]
  have hs2mem : s2 ∈ mkSegments d0 d1 d2 d3 d4 := by
    simp [s2, mkSegments]
  have hs3mem : s3 ∈ mkSegments d0 d1 d2 d3 d4 := by
    simp [s3, mkSegments]
  have hs4mem : s4 ∈ mkSegments d0 d1 d2 d3 d4 := by
    simp [s4, mkSegments]
  have h0raw := integral_Ioc_actualHybridIntegrand_le_sum_rectangles
    box s0 profile hprofile hh hlam hlamOne (by norm_num [s0])
      (by positivity) (hrow s0 hs0mem) (hcompact s0 hs0mem)
  have h1raw := integral_Ioc_actualHybridIntegrand_le_sum_rectangles
    box s1 profile hprofile hh hlam hlamOne (by norm_num [s1])
      (by positivity) (hrow s1 hs1mem) (hcompact s1 hs1mem)
  have h2raw := integral_Ioc_actualHybridIntegrand_le_sum_rectangles
    box s2 profile hprofile hh hlam hlamOne (by norm_num [s2])
      (by positivity) (hrow s2 hs2mem) (hcompact s2 hs2mem)
  have h3raw := integral_Ioc_actualHybridIntegrand_le_sum_rectangles
    box s3 profile hprofile hh hlam hlamOne (by norm_num [s3])
      (by positivity) (hrow s3 hs3mem) (hcompact s3 hs3mem)
  have h4raw := integral_Ioc_actualHybridIntegrand_le_sum_rectangles
    box s4 profile hprofile hh hlam hlamOne (by norm_num [s4])
      (by positivity) (hrow s4 hs4mem) (hcompact s4 hs4mem)
  have h0 : (∫ frequency : ℝ in Set.Ioc 0 1,
      actualHybridIntegrand box profile frequency) ≤
      segmentRectangleSum box s0 := by
    simpa [s0, segmentRectangleSum, hd0.ne'] using h0raw
  have h1 : (∫ frequency : ℝ in Set.Ioc 1 2,
      actualHybridIntegrand box profile frequency) ≤
      segmentRectangleSum box s1 := by
    convert h1raw using 1 <;>
      norm_num [s1, segmentRectangleSum, hd1.ne']
  have h2 : (∫ frequency : ℝ in Set.Ioc 2 4,
      actualHybridIntegrand box profile frequency) ≤
      segmentRectangleSum box s2 := by
    convert h2raw using 1 <;>
      norm_num [s2, segmentRectangleSum, hd2.ne']
  have h3 : (∫ frequency : ℝ in Set.Ioc 4 8,
      actualHybridIntegrand box profile frequency) ≤
      segmentRectangleSum box s3 := by
    convert h3raw using 1 <;>
      norm_num [s3, segmentRectangleSum, hd3.ne']
  have h4 : (∫ frequency : ℝ in Set.Ioc 8 8,
      actualHybridIntegrand box profile frequency) ≤
      segmentRectangleSum box s4 := by
    convert h4raw using 1 <;>
      norm_num [s4, segmentRectangleSum, hd4.ne']
  have hint := integrable_actualHybridIntegrand box profile hprofile
    hh hlam hlamOne
  change (∫ frequency : ℝ in Set.Ioc 0 8,
      actualHybridIntegrand box profile frequency) ≤ _
  rw [integral_Ioc_add hint (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 8)]
  rw [integral_Ioc_add hint (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 8)]
  rw [integral_Ioc_add hint (by norm_num : (2 : ℝ) ≤ 4) (by norm_num : (4 : ℝ) ≤ 8)]
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4
  simpa [mkSegments, s0, s1, s2, s3, s4, cutoff,
    segmentRectangleSum, add_assoc] using hsum

/-- Certificate-keyed wrapper for the five-segment finite aggregation. -/
theorem integral_Ioc_zero_cutoff_le_certificate_rectangleSums
    (certificate : CertificateBox) (profile : ℝ) (d0 d1 d2 d3 d4 : ℕ)
    (hsegments : certificate.segments = mkSegments d0 d1 d2 d3 d4)
    (hprofile : 0 ≤ profile)
    (hh : 0 < (certificate.box.uniformHalfWidth : ℝ))
    (hlam : 0 < (certificate.box.lam : ℝ))
    (hlamOne : (certificate.box.lam : ℝ) < 1)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hd3 : 0 < d3) (hd4 : 0 < d4)
    (hrow : ∀ segment ∈ certificate.segments,
      SegmentRowBounds certificate.box profile segment)
    (hcompact : ∀ segment ∈ certificate.segments,
      SegmentCompactBounds certificate.box segment) :
    (∫ frequency : ℝ in Set.Ioc 0 (cutoff : ℝ),
      actualHybridIntegrand certificate.box profile frequency) ≤
      (certificate.segments.map
        (segmentRectangleSum certificate.box)).sum := by
  rw [hsegments] at hrow hcompact ⊢
  exact integral_Ioc_zero_cutoff_le_mkSegments_rectangleSums
    certificate.box profile d0 d1 d2 d3 d4 hprofile hh hlam hlamOne
      hd0 hd1 hd2 hd3 hd4 hrow hcompact

end SparseUpperHybrid
end CertifiedJL
