/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.ClosedCore
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Soundness
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box00

/-!
# Closed contour core for the first legacy sparse upper box

This module integrates the signed row envelope over `(0,1/4]`.  Frequencies
above `1/4` remain available to the ordinary rectangle and analytic-tail
soundness layers.
-/

open MeasureTheory Set

namespace CertifiedJL
namespace SparseUpperContour
namespace ClosedCore

set_option maxRecDepth 100000

/-- A one-sided interval carrying the proved analytic core bound. -/
def firstBoxClosedCoreUpper : Interval contourPrecision :=
  let q := UpperContourKernel.frac contourPrecision (1669 / 25000)
  Interval.mk 0 q.hi

/-- Frozen first-box assembly with the first 25 rectangle cells replaced by
the closed analytic core.  The remaining 14 chunks and the tail at `15/4`
are byte-for-byte the shortened legacy certificate data. -/
def firstBoxClosedChunks : List (Interval contourPrecision) :=
  firstBoxClosedCoreUpper ::
    (SparseUpperContourData.Box00.chunks.drop 1).take 14

def firstBoxClosedBound : Interval contourPrecision :=
  ShortTail.boundFrom (profileBox 0) 15 firstBoxClosedChunks

/-- A coarse suffix chunk, parameterized by mesh, start, and count. -/
def firstBoxCoarseSuffix (mesh : ℚ) (start count : ℕ) : Interval contourPrecision :=
  (List.range count).foldl
    (fun result offset => result +
      gaussianCell (profileBox 0).profileLeft (profileBox 0).profileRight
        (profileBox 0).lam (profileBox 0).sigma mesh (start + offset))
    (UpperContourKernel.zero contourPrecision)

def firstBoxCoarseClosedIntegralFor
    (mesh : ℚ) (start count : ℕ) : Interval contourPrecision :=
  let raw := ShortTail.integralFrom (profileBox 0) 15
    [firstBoxClosedCoreUpper, firstBoxCoarseSuffix mesh start count]
  Interval.mk 0 raw.hi

def firstBoxCoarseClosedBoundFor (mesh : ℚ) (start count : ℕ) : Interval contourPrecision :=
  boxPrefactor (profileBox 0) * firstBoxCoarseClosedIntegralFor mesh start count

def firstBoxCoarseClosedIntegral : Interval contourPrecision :=
  firstBoxCoarseClosedIntegralFor (1 / 40) 10 140

def firstBoxCoarseClosedBound : Interval contourPrecision :=
  boxPrefactor (profileBox 0) * firstBoxCoarseClosedIntegral

/-- Numerical certificate boundary for the closed-core first-box route.
Its kernel provider lives in `Replay.ClosedCoreFirstBox`. -/
def FirstBoxCoarseClosedBudget : Prop :=
  Interval.upperLTCheck firstBoxCoarseClosedBound (profileBox 0).target = true

private theorem profileBox_rowExpression_contains_mesh
    {box : ProfileBox} (hbox : box ∈ profileBoxes) (profileQ mesh : ℚ)
    (hprofileQ : 0 ≤ profileQ) (hmesh : 0 < mesh) (index : ℕ) (frequency : ℝ)
    (hfrequency : frequency ∈ Set.Ioc
      (((((index : ℕ) : ℚ) * mesh : ℚ) : ℝ))
      ((((index + 1 : ℕ) : ℚ) * mesh : ℚ) : ℝ)) :
    (rowExpressionOnCell profileQ (index * mesh) ((index + 1) * mesh) box.lam).Contains
      (UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
        profileQ box.lam frequency) := by
  let frequencyLeft : ℚ := index * mesh
  let frequencyRight : ℚ := (index + 1) * mesh
  let frequencyInterval := Interval.enclose contourPrecision
    frequencyLeft frequencyRight
  have hleftNonneg : 0 ≤ frequencyLeft := by
    dsimp only [frequencyLeft]
    positivity
  have hleftRight : frequencyLeft ≤ frequencyRight := by
    dsimp only [frequencyLeft, frequencyRight]
    have hi : (index : ℚ) ≤ (index : ℚ) + 1 :=
      le_add_of_nonneg_right (by norm_num)
    exact mul_le_mul_of_nonneg_right hi hmesh.le
  have hfrequencyInterval : frequencyInterval.Contains (frequencyLeft : ℝ) :=
    Interval.contains_enclose ⟨le_rfl, by exact_mod_cast hleftRight⟩
  have hfrequencyValid : frequencyInterval.Valid :=
    Interval.valid_of_contains hfrequencyInterval
  have hfrequencyLo : 0 ≤ frequencyInterval.lo :=
    Dyadic.roundDown_nonneg hleftNonneg
  have hsquareLo : 0 ≤ frequencyInterval.square.lo :=
    Interval.square_lo_nonneg_of_lo_nonneg hfrequencyValid hfrequencyLo
  have honeMinusLo : 0 ≤
      (UpperContourKernel.frac contourPrecision (1 - box.lam)).lo := by
    exact Dyadic.roundDown_nonneg (by
      obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox
      linarith)
  have honeSquarePos : 0 <
      (UpperContourKernel.frac contourPrecision
        ((1 - box.lam) * (1 - box.lam))).lo := by
    have hcase := hbox
    simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcase
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel
  have hdenominator : 0 <
      (UpperContourKernel.frac contourPrecision
        ((1 - box.lam) * (1 - box.lam)) + frequencyInterval.square).lo :=
    add_pos_of_pos_of_nonneg honeSquarePos hsquareLo
  have hgaussianDenominator : 0 <
      ((UpperContourKernel.frac contourPrecision
        ((1 - box.lam) * (1 - box.lam)) + frequencyInterval.square).sqrt.sqrt).lo :=
    Interval.sqrt_lo_pos_of_lo_pos (Interval.sqrt_lo_pos_of_lo_pos hdenominator)
  have hrho : 0 ≤
      (UpperContourKernel.frac contourPrecision (box.lam * box.lam) +
        frequencyInterval.square).lo := by
    exact add_nonneg (Dyadic.roundDown_nonneg (mul_self_nonneg box.lam)) hsquareLo
  apply UpperContourKernel.contains_normalizedFourthOrderRowBound
  · obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox
    exact_mod_cast hlamOne
  · constructor
    · exact hfrequency.1.le
    · push_cast at hfrequency ⊢
      exact hfrequency.2
  · exact honeMinusLo
  · exact hdenominator
  · exact hgaussianDenominator
  · exact hrho
  · exact Or.inr (Dyadic.roundDown_nonneg hprofileQ)

private theorem normalizedFourthOrderRowBound_nonneg_mesh
    (profile lam : ℚ) (frequency : ℝ) (hprofile : 0 ≤ profile)
    (hlam : (lam : ℝ) < 1) :
    0 ≤ UpperContourKernel.normalizedFourthOrderRowBound
      rowCoefficients profile lam frequency := by
  rw [normalizedFourthOrderRowBound_eq_sparseUpperMajorant profile lam frequency hlam]
  unfold sparseUpperFourthOrderNormalizedMajorant
  have hd8 := quadraticExpDerivativeMajorant_nonneg (m := 8)
    (norm_nonneg ((lam : ℝ) + frequency * Complex.I)) hlam
  have hd6 := quadraticExpDerivativeMajorant_nonneg (m := 6)
    (norm_nonneg ((lam : ℝ) + frequency * Complex.I)) hlam
  positivity

private theorem profileBox_profile_facts_mesh {box : ProfileBox}
    (hbox : box ∈ profileBoxes) : 0 ≤ box.profileLeft ∧ box.profileLeft ≤ box.profileRight := by
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

/-- The profile-box row bridge works unchanged on a positive rational mesh. -/
theorem profileBox_rowMajorant_le_gaussianCellRowUpperValue_mesh
    {box : ProfileBox} (hbox : box ∈ profileBoxes) {profile frequency : ℝ}
    (hprofile : profile ∈ Set.Icc (box.profileLeft : ℝ) (box.profileRight : ℝ))
    (mesh : ℚ) (hmesh : 0 < mesh) (index : ℕ)
    (hfrequency : frequency ∈ Set.Ioc
      ((((index : ℕ) : ℚ) * mesh : ℚ) : ℝ)
      (((((index + 1 : ℕ) : ℚ) * mesh : ℚ) : ℝ))) :
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      gaussianCellRowUpperValue box.profileLeft box.profileRight box.lam mesh index := by
  apply sparseUpperContourRowMajorant_le_gaussianCellRowUpperValue
  · exact_mod_cast (profileBox_profile_facts_mesh hbox).1
  · exact hprofile
  · obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox
    exact_mod_cast hlamOne
  · exact profileBox_rowExpression_contains_mesh hbox box.profileLeft mesh
      (profileBox_profile_facts_mesh hbox).1 hmesh index frequency hfrequency
  · exact profileBox_rowExpression_contains_mesh hbox box.profileRight mesh
      ((profileBox_profile_facts_mesh hbox).1.trans (profileBox_profile_facts_mesh hbox).2)
      hmesh index frequency hfrequency
  · exact profileBox_realCapUpper_contains hbox hprofile

private theorem integer_nonneg_of_toReal_nonneg
    {p : ℕ} {x : ℤ} (hx : 0 ≤ Dyadic.toReal p x) : 0 ≤ x := by
  rw [Dyadic.toReal] at hx
  have hs : (0 : ℝ) < Dyadic.scale p := by exact_mod_cast Dyadic.scale_pos p
  by_contra hneg
  have hxneg : (x : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hneg)
  exact (not_le_of_gt (div_neg_of_neg_of_pos hxneg hs)) hx

/-- The executable Gaussian cell remains sound on every positive rational mesh. -/
theorem profileBox_gaussianCell_contains_rectangle_mesh
    {box : ProfileBox} (hbox : box ∈ profileBoxes) (mesh : ℚ)
    (hmesh : 0 < mesh) (index : ℕ) :
    (gaussianCell box.profileLeft box.profileRight box.lam box.sigma mesh index).Contains
      (gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma mesh index) := by
  let right : ℚ := (index + 1) * mesh
  have hrightMem : (right : ℝ) ∈ Set.Ioc
      ((((index : ℕ) : ℚ) * mesh : ℚ) : ℝ) (right : ℝ) := by
    dsimp only [right]
    constructor
    · exact_mod_cast (mul_lt_mul_of_pos_right
        (show (index : ℚ) < (index + 1 : ℕ) by exact_mod_cast index.lt_succ_self) hmesh)
    · exact le_rfl
  have hleftRight : box.profileLeft ≤ box.profileRight :=
    (profileBox_profile_facts_mesh hbox).2
  have hrow := profileBox_rowMajorant_le_gaussianCellRowUpperValue_mesh hbox
    (profile := (box.profileLeft : ℝ)) (frequency := (right : ℝ))
    ⟨le_rfl, by exact_mod_cast hleftRight⟩ mesh hmesh index (by simpa [right] using hrightMem)
  have hrowNonneg := sparseUpperContourRowMajorant_nonneg
    (profile := (box.profileLeft : ℝ)) (lambda := (box.lam : ℝ))
    (frequency := (right : ℝ))
    (by exact_mod_cast (profileBox_profile_facts_mesh hbox).1)
    (by obtain ⟨_, _, _, hlam, _, _, _, _⟩ := profileBox_numeric_facts hbox;
        exact_mod_cast hlam.le)
    (by obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox;
        exact_mod_cast hlamOne)
  have hselected : 0 ≤
      gaussianCellRowUpperValue box.profileLeft box.profileRight box.lam mesh index :=
    hrowNonneg.trans hrow
  have hrowUpper : 0 ≤
      min (realCapUpper contourPrecision box.profileLeft box.lam).hi
        (max
          (rowExpressionOnCell box.profileLeft (index * mesh)
            ((index + 1) * mesh) box.lam).hi
          (rowExpressionOnCell box.profileRight (index * mesh)
            ((index + 1) * mesh) box.lam).hi) := by
    apply integer_nonneg_of_toReal_nonneg
    simpa only [gaussianCellRowUpperValue] using hselected
  apply gaussianCell_contains_rectangle
  · exact hrowUpper
  · apply Dyadic.roundDown_nonneg
    exact add_nonneg (mul_self_nonneg box.lam) (mul_self_nonneg (index * mesh))
  · apply Interval.sqrt_lo_pos_of_lo_pos
    apply Dyadic.roundDown_pos
    have hfixed : 1 ≤ box.lam * box.lam * Dyadic.scale contourPrecision := by
      have hcase := hbox
      simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcase
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide +kernel
    have hfreq : 0 ≤ (index * mesh) * (index * mesh) := mul_self_nonneg _
    nlinarith [mul_nonneg hfreq (by positivity : (0 : ℚ) ≤ Dyadic.scale contourPrecision)]

private theorem actualBoxQuadratureIntegrand_le_rectangle_mesh
    (box : ProfileBox) (profile frequency : ℝ) (mesh : ℚ) (index : ℕ)
    (hprofile : 0 ≤ profile) (hlam : 0 < (box.lam : ℝ))
    (hlamOne : (box.lam : ℝ) < 1) (hmesh : 0 < mesh)
    (hfrequency : ((((index : ℕ) : ℚ) * mesh : ℚ) : ℝ) ≤ frequency)
    (hrow : sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      gaussianCellRowUpperValue box.profileLeft box.profileRight box.lam mesh index) :
    (mesh : ℝ) * actualBoxQuadratureIntegrand box profile frequency ≤
      gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma mesh index := by
  let left : ℝ := ((((index : ℕ) : ℚ) * mesh : ℚ) : ℝ)
  have hleft : 0 ≤ left := by dsimp only [left]; positivity
  have hweight := gaussianQuadratureWeight_le_of_le
    (alpha := (box.sigma : ℝ) ^ 2 / 2)
    (lambda := (box.lam : ℝ)) (frequencyLeft := left)
    (frequency := frequency) (by positivity) hlam hleft hfrequency
  have hrowNonneg := sparseUpperContourRowMajorant_nonneg
    (frequency := frequency) hprofile hlam.le hlamOne
  have hrowPower := pow_le_pow_left₀ hrowNonneg hrow rows
  have hweightLeftNonneg : 0 ≤
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * left ^ 2) *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + left ^ 2)) := by positivity
  have hproduct := mul_le_mul hweight hrowPower (pow_nonneg hrowNonneg rows)
    hweightLeftNonneg
  unfold actualBoxQuadratureIntegrand gaussianCellRectangleValue
  dsimp only
  change (mesh : ℝ) *
      (Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
        sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^ rows *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) ≤ _
  calc
    _ = (mesh : ℝ) *
        ((Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) *
          sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^ rows) := by ring
    _ ≤ (mesh : ℝ) *
        ((Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * left ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + left ^ 2))) *
          gaussianCellRowUpperValue box.profileLeft box.profileRight
            box.lam mesh index ^ rows) :=
      mul_le_mul_of_nonneg_left hproduct (by exact_mod_cast hmesh.le)
    _ = _ := by
      dsimp only [left]
      push_cast
      norm_num [rows]
      ring

noncomputable def coarseRectangleCells
    (box : ProfileBox) (mesh : ℚ) (start count : ℕ) : ℝ :=
  (List.range count).foldl
    (fun result offset => result +
      gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma mesh (start + offset)) 0

/-- A consecutive positive-mesh cell range dominates the corresponding
actual contour-integral interval. -/
theorem integral_Ioc_actualBoxQuadratureIntegrand_le_coarseRectangles
    (box : ProfileBox) (profile : ℝ) (mesh : ℚ) (start count : ℕ)
    (hprofile : 0 ≤ profile) (hlam : 0 < (box.lam : ℝ))
    (hlamOne : (box.lam : ℝ) < 1) (hmesh : 0 < mesh)
    (hrow : ∀ offset < count, ∀ frequency ∈ Set.Ioc
      (((((start + offset : ℕ) : ℚ) * mesh : ℚ) : ℝ))
      (((((start + offset + 1 : ℕ) : ℚ) * mesh : ℚ) : ℝ)),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue box.profileLeft box.profileRight
          box.lam mesh (start + offset)) :
    (∫ frequency : ℝ in Set.Ioc
      (((((start : ℕ) : ℚ) * mesh : ℚ) : ℝ))
      (((((start + count : ℕ) : ℚ) * mesh : ℚ) : ℝ)),
      actualBoxQuadratureIntegrand box profile frequency) ≤
        coarseRectangleCells box mesh start count := by
  have hcontinuous := continuous_actualBoxQuadratureIntegrand box profile hlam hlamOne
  induction count with
  | zero => simp [coarseRectangleCells]
  | succ count ih =>
      have hrowPrevious : ∀ offset < count, ∀ frequency ∈ Set.Ioc
          (((((start + offset : ℕ) : ℚ) * mesh : ℚ) : ℝ))
          (((((start + offset + 1 : ℕ) : ℚ) * mesh : ℚ) : ℝ)),
          sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
            gaussianCellRowUpperValue box.profileLeft box.profileRight
              box.lam mesh (start + offset) := by
        intro offset hoffset
        exact hrow offset (hoffset.trans count.lt_succ_self)
      have hprevious := ih hrowPrevious
      let base : ℝ := ((((start : ℕ) : ℚ) * mesh : ℚ) : ℝ)
      let left : ℝ := ((((start + count : ℕ) : ℚ) * mesh : ℚ) : ℝ)
      let right : ℝ := ((((start + count + 1 : ℕ) : ℚ) * mesh : ℚ) : ℝ)
      let rectangle := gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma mesh (start + count)
      have hbaseLeft : base ≤ left := by
        dsimp only [base, left]
        have hq : (start : ℚ) * mesh ≤ ((start + count : ℕ) : ℚ) * mesh :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right start count) hmesh.le
        exact_mod_cast hq
      have hleftRight : left ≤ right := by
        dsimp only [left, right]
        have hq : ((start + count : ℕ) : ℚ) * mesh ≤
            ((start + count + 1 : ℕ) : ℚ) * mesh :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ (start + count)) hmesh.le
        exact_mod_cast hq
      have hcellPointwise : ∀ frequency ∈ Set.Ioc left right,
          actualBoxQuadratureIntegrand box profile frequency ≤ rectangle / (mesh : ℝ) := by
        intro frequency hfrequency
        apply (le_div_iff₀ (by exact_mod_cast hmesh)).2
        dsimp only [left, right, rectangle] at hfrequency ⊢
        have hfrequencyLeft :
            (((((start + count : ℕ) : ℚ) * mesh : ℚ) : ℝ)) ≤ frequency :=
          hfrequency.1.le
        simpa only [mul_comm] using
          actualBoxQuadratureIntegrand_le_rectangle_mesh box profile frequency mesh
            (start + count) hprofile hlam hlamOne hmesh hfrequencyLeft
            (hrow count count.lt_succ_self frequency (by
              push_cast at hfrequency ⊢
              simpa [add_assoc] using hfrequency))
      have hcell :
          (∫ frequency : ℝ in Set.Ioc left right,
            actualBoxQuadratureIntegrand box profile frequency) ≤ rectangle := by
        calc
          _ ≤ ∫ _frequency : ℝ in Set.Ioc left right, rectangle / (mesh : ℝ) := by
            apply setIntegral_mono_on
            · exact hcontinuous.continuousOn.integrableOn_Icc.mono_set
                Set.Ioc_subset_Icc_self
            · exact integrableOn_const (hs := by
                rw [Real.volume_Ioc]
                exact ENNReal.ofReal_ne_top)
            · exact measurableSet_Ioc
            · exact hcellPointwise
          _ = rectangle := by
            rw [setIntegral_const]
            simp only [smul_eq_mul, Measure.real, Real.volume_Ioc]
            rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hleftRight)]
            dsimp only [left, right]
            push_cast
            field_simp
            ring
      have hdisjoint : Disjoint (Set.Ioc base left) (Set.Ioc left right) :=
        Set.disjoint_left.2 fun _ hx hy => (not_lt_of_ge hx.2) hy.1
      have hunion : Set.Ioc base left ∪ Set.Ioc left right = Set.Ioc base right := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc]
        constructor
        · rintro (hx | hx)
          · exact ⟨hx.1, hx.2.trans hleftRight⟩
          · exact ⟨lt_of_le_of_lt hbaseLeft hx.1, hx.2⟩
        · intro hx
          by_cases hxl : x ≤ left
          · exact Or.inl ⟨hx.1, hxl⟩
          · exact Or.inr ⟨lt_of_not_ge hxl, hx.2⟩
      change (∫ frequency : ℝ in Set.Ioc base right,
        actualBoxQuadratureIntegrand box profile frequency) ≤
          coarseRectangleCells box mesh start (count + 1)
      rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioc
        (hcontinuous.integrableOn_Ioc) (hcontinuous.integrableOn_Ioc)]
      unfold coarseRectangleCells at hprevious ⊢
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact add_le_add hprevious hcell

/-- The row envelope, raised to all 512 rows and combined with the contour
Gaussian and radial factor. -/
theorem firstBox_integrand_le_closedGaussian
    {profile frequency : ℝ}
    (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024))
    (hfrequency : frequency ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    actualBoxQuadratureIntegrand (profileBox 0) profile frequency ≤
      (1000 / 579 : ℝ) *
        Real.exp (-(1055272049 / 2000000 : ℝ) * frequency ^ 2) := by
  have hrow := rowMajorant_le_closedGaussian hprofile hfrequency
  have hrow0 := sparseUpperContourRowMajorant_nonneg
    (frequency := frequency) hprofile.1 (by norm_num : (0 : ℝ) ≤ 579 / 1000)
      (by norm_num : (579 / 1000 : ℝ) < 1)
  have hrowPower := pow_le_pow_left₀ hrow0 hrow 512
  have hsqrt : (579 / 1000 : ℝ) ≤
      Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).2
      (by nlinarith [sq_nonneg frequency])
  have hinverse :
      1 / Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) ≤
        (1000 / 579 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 579 / 1000) hsqrt
  have hgaussian0 : 0 ≤ Real.exp (-(743 / 1000 : ℝ) ^ 2 / 2 * frequency ^ 2) :=
    Real.exp_nonneg _
  have hinverse0 : 0 ≤ 1 / Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) := by
    positivity
  have hmain :
    Real.exp (-((743 / 1000 : ℝ) ^ 2 / 2 * frequency ^ 2)) *
          sparseUpperContourRowMajorant profile (579 / 1000) frequency ^ 512 *
          (1 / Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2)) ≤
          (1000 / 579 : ℝ) *
            Real.exp (-(1055272049 / 2000000 : ℝ) * frequency ^ 2) := by
    calc
      _ ≤ Real.exp (-((743 / 1000 : ℝ) ^ 2 / 2 * frequency ^ 2)) *
            (Real.exp (-(103 / 100 : ℝ) * frequency ^ 2)) ^ 512 *
            (1000 / 579 : ℝ) := by gcongr
      _ = _ := by
        have hexp :
            Real.exp (-((743 / 1000 : ℝ) ^ 2 / 2 * frequency ^ 2)) *
                (Real.exp (-(103 / 100 : ℝ) * frequency ^ 2)) ^ 512 =
              Real.exp (-(1055272049 / 2000000 : ℝ) * frequency ^ 2) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
  simpa [actualBoxQuadratureIntegrand, profileBox, firstBox, profileBoxes, rows] using hmain

private theorem integral_Ioi_exp_neg_mul_sq
    {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, Real.exp (-c * x ^ 2)) =
      Real.sqrt (Real.pi / c) / 2 := by
  let f : ℝ → ℝ := fun x => Real.exp (-c * x ^ 2)
  have hf : Integrable f := by
    simpa only [f] using integrable_exp_neg_mul_sq hc
  have heven (x : ℝ) : f (-x) = f x := by simp only [f, neg_sq]
  have hleft :
      (∫ x : ℝ in Set.Iic 0, f x) = ∫ x : ℝ in Set.Ioi 0, f x := by
    calc
      (∫ x : ℝ in Set.Iic 0, f x) =
          ∫ x : ℝ in Set.Iic 0, f (-x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x _
        exact (heven x).symm
      _ = ∫ x : ℝ in Set.Ioi 0, f x := by simp
  have hsplit := integral_add_compl (μ := volume) (s := Set.Ioi (0 : ℝ))
    measurableSet_Ioi hf
  rw [compl_Ioi, hleft] at hsplit
  have hfull : (∫ x : ℝ, f x) = Real.sqrt (Real.pi / c) := by
    simpa only [f] using integral_gaussian c
  rw [hfull] at hsplit
  linarith

private theorem closedGaussian_integral_lt :
    (1000 / 579 : ℝ) *
        (∫ frequency : ℝ in Set.Ioi 0,
          Real.exp (-(1055272049 / 2000000 : ℝ) * frequency ^ 2)) <
      1669 / 25000 := by
  rw [integral_Ioi_exp_neg_mul_sq (by norm_num)]
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hratio :
      Real.pi / (1055272049 / 2000000 : ℝ) <
        (773 / 10000 : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1055272049 / 2000000)]
    nlinarith
  have hsqrt :
      Real.sqrt (Real.pi / (1055272049 / 2000000 : ℝ)) <
        773 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 773 / 10000)]
    exact hratio
  nlinarith

/-- The complete `(0,1/4]` core costs less than the rational `1669/25000`.
This is a bound on the actual canonical contour integrand, not on an evaluator
surrogate. -/
theorem firstBox_core_integral_lt
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    (∫ frequency : ℝ in Set.Ioc 0 (1 / 4),
      actualBoxQuadratureIntegrand (profileBox 0) profile frequency) <
      1669 / 25000 := by
  let envelope : ℝ → ℝ := fun frequency =>
    (1000 / 579 : ℝ) *
      Real.exp (-(1055272049 / 2000000 : ℝ) * frequency ^ 2)
  have hp0 : 0 ≤ profile := hprofile.1
  have hactual := integrable_actualBoxQuadratureIntegrand
    (profileBox 0) profile hp0 (by norm_num [profileBox, firstBox, profileBoxes])
      (by norm_num [profileBox, firstBox, profileBoxes])
      (by norm_num [profileBox, firstBox, profileBoxes])
  have henvelope : Integrable envelope :=
    (integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1055272049 / 2000000)).const_mul _
  have hcore :
      (∫ frequency : ℝ in Set.Ioc 0 (1 / 4),
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) ≤
      ∫ frequency : ℝ in Set.Ioc 0 (1 / 4), envelope frequency := by
    apply setIntegral_mono_on hactual.integrableOn henvelope.integrableOn measurableSet_Ioc
    intro frequency hfrequency
    exact firstBox_integrand_le_closedGaussian hprofile ⟨hfrequency.1.le, hfrequency.2⟩
  have hset :
      (∫ frequency : ℝ in Set.Ioc 0 (1 / 4), envelope frequency) ≤
        ∫ frequency : ℝ in Set.Ioi 0, envelope frequency := by
    apply setIntegral_mono_set henvelope.integrableOn
    · exact ae_of_all _ fun frequency => by dsimp only [envelope]; positivity
    · exact ae_of_all _ fun _ hfrequency => hfrequency.1
  exact hcore.trans_lt (hset.trans_lt (by
    simpa only [envelope, MeasureTheory.integral_const_mul] using closedGaussian_integral_lt))

private theorem firstBox_core_integral_nonneg
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    0 ≤ ∫ frequency : ℝ in Set.Ioc 0 (1 / 4),
      actualBoxQuadratureIntegrand (profileBox 0) profile frequency := by
  apply setIntegral_nonneg measurableSet_Ioc
  intro frequency _
  unfold actualBoxQuadratureIntegrand
  have hrow : 0 ≤ sparseUpperContourRowMajorant profile
      ((profileBox 0).lam : ℝ) frequency :=
    sparseUpperContourRowMajorant_nonneg hprofile.1
      (by norm_num [profileBox, firstBox, profileBoxes])
      (by norm_num [profileBox, firstBox, profileBoxes])
  exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hrow rows)) (by positivity)

theorem firstBoxClosedCoreUpper_contains
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    firstBoxClosedCoreUpper.Contains
      (∫ frequency : ℝ in Set.Ioc 0 (1 / 4),
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) := by
  have hq := Interval.contains_ofRat contourPrecision (1669 / 25000 : ℚ)
  constructor
  · simpa [firstBoxClosedCoreUpper] using firstBox_core_integral_nonneg hprofile
  · apply (firstBox_core_integral_lt hprofile).le.trans
    change (1669 / 25000 : ℝ) ≤ Dyadic.toReal contourPrecision
      (UpperContourKernel.frac contourPrecision (1669 / 25000)).hi
    have hcast : (((1669 / 25000 : ℚ) : ℝ)) = (1669 / 25000 : ℝ) := by norm_num
    rw [← hcast]
    simpa only [UpperContourKernel.frac] using hq.2

theorem firstBoxCoarseSuffix_contains :
    (firstBoxCoarseSuffix (1 / 40) 10 140).Contains
      (coarseRectangleCells (profileBox 0) (1 / 40) 10 140) := by
  have hbox : profileBox 0 ∈ profileBoxes := by
    norm_num [profileBox, firstBox, profileBoxes]
  have hzero : (UpperContourKernel.zero contourPrecision).Contains (0 : ℝ) := by
    simpa [UpperContourKernel.zero, UpperContourKernel.frac] using
      Interval.contains_ofRat contourPrecision (0 : ℚ)
  unfold firstBoxCoarseSuffix coarseRectangleCells
  apply Internal.contains_foldl_add (List.range 140)
    (fun offset => gaussianCell (profileBox 0).profileLeft (profileBox 0).profileRight
      (profileBox 0).lam (profileBox 0).sigma (1 / 40) (10 + offset))
    (fun offset => gaussianCellRectangleValue
      (profileBox 0).profileLeft (profileBox 0).profileRight
      (profileBox 0).lam (profileBox 0).sigma (1 / 40) (10 + offset))
  · intro offset _
    exact profileBox_gaussianCell_contains_rectangle_mesh hbox (1 / 40)
      (by norm_num) (10 + offset)
  · exact hzero

theorem firstBox_suffix_integral_le
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    (∫ frequency : ℝ in Set.Ioc (1 / 4) (15 / 4),
      actualBoxQuadratureIntegrand (profileBox 0) profile frequency) ≤
        coarseRectangleCells (profileBox 0) (1 / 40) 10 140 := by
  have hbox : profileBox 0 ∈ profileBoxes := by
    norm_num [profileBox, firstBox, profileBoxes]
  have hprofileBox : profile ∈ Set.Icc
      ((profileBox 0).profileLeft : ℝ) ((profileBox 0).profileRight : ℝ) := by
    simpa [profileBox, firstBox, profileBoxes] using hprofile
  have h := integral_Ioc_actualBoxQuadratureIntegrand_le_coarseRectangles
    (profileBox 0) profile (1 / 40) 10 140 hprofile.1
    (by norm_num [profileBox, firstBox, profileBoxes])
    (by norm_num [profileBox, firstBox, profileBoxes]) (by norm_num)
    (fun offset _ frequency hfrequency =>
      profileBox_rowMajorant_le_gaussianCellRowUpperValue_mesh hbox hprofileBox
        (1 / 40) (by norm_num) (10 + offset) (by
          push_cast at hfrequency ⊢
          simpa only [add_assoc] using hfrequency))
  convert h using 1
  all_goals norm_num

private theorem firstBox_integral_le_surrogate
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    (∫ frequency : ℝ in Set.Ioi 0,
      actualBoxQuadratureIntegrand (profileBox 0) profile frequency) ≤
      (∫ frequency : ℝ in Set.Ioc 0 (1 / 4),
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) +
        coarseRectangleCells (profileBox 0) (1 / 40) 10 140 +
        ShortTail.tailValue (profileBox 0) profile (15 / 4) := by
  have hint := integrable_actualBoxQuadratureIntegrand
    (profileBox 0) profile hprofile.1
    (by norm_num [profileBox, firstBox, profileBoxes])
    (by norm_num [profileBox, firstBox, profileBoxes])
    (by norm_num [profileBox, firstBox, profileBoxes])
  have hcoreSuffix : Disjoint (Set.Ioc (0 : ℝ) (1 / 4)) (Set.Ioi (1 / 4)) :=
    Set.disjoint_left.2 fun _ hx hy => (not_lt_of_ge hx.2) hy
  have hunionCore : Set.Ioc (0 : ℝ) (1 / 4) ∪ Set.Ioi (1 / 4) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · linarith
    · intro hx
      by_cases hxc : x ≤ 1 / 4
      · exact Or.inl ⟨hx, hxc⟩
      · exact Or.inr (lt_of_not_ge hxc)
  have hsuffixTail : Disjoint (Set.Ioc (1 / 4 : ℝ) (15 / 4)) (Set.Ioi (15 / 4)) :=
    Set.disjoint_left.2 fun _ hx hy => (not_lt_of_ge hx.2) hy
  have hunionSuffix :
      Set.Ioc (1 / 4 : ℝ) (15 / 4) ∪ Set.Ioi (15 / 4) = Set.Ioi (1 / 4) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · linarith
    · intro hx
      by_cases hxc : x ≤ 15 / 4
      · exact Or.inl ⟨hx, hxc⟩
      · exact Or.inr (lt_of_not_ge hxc)
  have hsuffix := firstBox_suffix_integral_le hprofile
  have htail := ShortTail.tail_integral_le (profileBox 0) profile (15 / 4)
    (by norm_num) hprofile.1
    (by norm_num [profileBox, firstBox, profileBoxes])
    (by norm_num [profileBox, firstBox, profileBoxes])
    (by norm_num [profileBox, firstBox, profileBoxes])
  rw [← hunionCore, setIntegral_union hcoreSuffix measurableSet_Ioi
    hint.integrableOn hint.integrableOn]
  rw [← hunionSuffix, setIntegral_union hsuffixTail measurableSet_Ioi
    hint.integrableOn hint.integrableOn]
  linarith

theorem firstBoxCoarseClosedIntegral_contains
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    firstBoxCoarseClosedIntegral.Contains
      (∫ frequency : ℝ in Set.Ioi 0,
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) := by
  let coreValue := ∫ frequency : ℝ in Set.Ioc 0 (1 / 4),
    actualBoxQuadratureIntegrand (profileBox 0) profile frequency
  let cellsValue := coarseRectangleCells (profileBox 0) (1 / 40) 10 140
  let tailValue := ShortTail.tailValue (profileBox 0) profile (15 / 4)
  have hcore : firstBoxClosedCoreUpper.Contains coreValue :=
    firstBoxClosedCoreUpper_contains hprofile
  have hcells : (firstBoxCoarseSuffix (1 / 40) 10 140).Contains cellsValue :=
    firstBoxCoarseSuffix_contains
  have htail := ShortTail.tail_contains (profileBox 0) profile (15 / 4)
    (profileBox_realCapUpper_contains
      (by norm_num [profileBox, firstBox, profileBoxes]) (by
        simpa [profileBox, firstBox, profileBoxes] using hprofile))
  have hraw :
      (ShortTail.integralFrom (profileBox 0) 15
        [firstBoxClosedCoreUpper, firstBoxCoarseSuffix (1 / 40) 10 140]).Contains
          (coreValue + cellsValue + tailValue) := by
    have hzero : (UpperContourKernel.zero contourPrecision).Contains (0 : ℝ) := by
      simpa [UpperContourKernel.zero, UpperContourKernel.frac] using
        Interval.contains_ofRat contourPrecision (0 : ℚ)
    have := Interval.contains_add
      (Interval.contains_add (Interval.contains_add hzero hcore) hcells) htail
    simpa [ShortTail.integralFrom, coreValue, cellsValue, tailValue,
      UpperContourKernel.zero] using this
  have hle :
      (∫ frequency : ℝ in Set.Ioi 0,
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) ≤
          coreValue + cellsValue + tailValue := by
    simpa [coreValue, cellsValue, tailValue, add_assoc] using
      firstBox_integral_le_surrogate hprofile
  have hnonneg : 0 ≤ ∫ frequency : ℝ in Set.Ioi 0,
      actualBoxQuadratureIntegrand (profileBox 0) profile frequency := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    unfold actualBoxQuadratureIntegrand
    have hrow : 0 ≤ sparseUpperContourRowMajorant profile
        ((profileBox 0).lam : ℝ) frequency :=
      sparseUpperContourRowMajorant_nonneg hprofile.1
        (by norm_num [profileBox, firstBox, profileBoxes])
        (by norm_num [profileBox, firstBox, profileBoxes])
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hrow rows)) (by positivity)
  constructor
  · simpa [firstBoxCoarseClosedIntegral, firstBoxCoarseClosedIntegralFor] using hnonneg
  · exact hle.trans (by
      simpa [firstBoxCoarseClosedIntegral, firstBoxCoarseClosedIntegralFor] using hraw.2)

/-- Semantic first-box endpoint conditional on its numerical certificate:
the closed core, 140 coarse suffix cells, and shortened analytic tail preserve
the original strict `97/100`. The unconditional provider is isolated in replay. -/
theorem firstBox_coarse_closed_endpoint_of_budget
    (budget : FirstBoxCoarseClosedBudget)
    {profile : ℝ} (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024)) :
    boxActualPrefactorValue (profileBox 0) *
      (∫ frequency : ℝ in Set.Ioi 0,
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) <
      (97 / 100 : ℝ) := by
  have hbox : profileBox 0 ∈ profileBoxes := by
    norm_num [profileBox, firstBox, profileBoxes]
  obtain ⟨_, _, _, _, _, _, hexponent, _⟩ := profileBox_numeric_facts hbox
  have hintegral := firstBoxCoarseClosedIntegral_contains hprofile
  have hprefactor := boxPrefactor_contains_rationalValue (profileBox 0) hexponent
  have hproduct := Interval.contains_mul hprefactor hintegral
  have hactualPrefactor := boxActualPrefactorValue_le_rationalValue hbox
  have hwholeNonneg : 0 ≤ ∫ frequency : ℝ in Set.Ioi 0,
      actualBoxQuadratureIntegrand (profileBox 0) profile frequency := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    unfold actualBoxQuadratureIntegrand
    have hrow : 0 ≤ sparseUpperContourRowMajorant profile
        ((profileBox 0).lam : ℝ) frequency :=
      sparseUpperContourRowMajorant_nonneg hprofile.1
        (by norm_num [profileBox, firstBox, profileBoxes])
        (by norm_num [profileBox, firstBox, profileBoxes])
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hrow rows)) (by positivity)
  have hmul := mul_le_mul hactualPrefactor le_rfl hwholeNonneg
    (by
      unfold boxRationalPrefactorValue
      dsimp only
      norm_num [profileBox, firstBox, profileBoxes, rows, securityBits]
      positivity)
  have hupper : boxRationalPrefactorValue (profileBox 0) *
      (∫ frequency : ℝ in Set.Ioi 0,
        actualBoxQuadratureIntegrand (profileBox 0) profile frequency) ≤
      (firstBoxCoarseClosedBound.upperRat : ℝ) := by
    simpa only [firstBoxCoarseClosedBound,
      Interval.upperRat, Dyadic.cast_toRat] using hproduct.2
  have hbudget : firstBoxCoarseClosedBound.upperRat < 97 / 100 := by
    simpa [profileBox, firstBox, profileBoxes] using
      Interval.upperLTCheck_sound budget
  have hbudgetReal := (Rat.cast_lt (K := ℝ)).2 hbudget
  exact hmul.trans_lt (hupper.trans_lt (by norm_num at hbudgetReal ⊢; exact hbudgetReal))

end ClosedCore
end SparseUpperContour
end CertifiedJL
