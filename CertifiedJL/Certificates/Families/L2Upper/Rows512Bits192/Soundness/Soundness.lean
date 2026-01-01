/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.AnalyticCore

/-! Legacy quadrature assembly, separate from the shared analytic facts. -/

namespace CertifiedJL
namespace SparseUpperContour

set_option maxRecDepth 100000
open MeasureTheory ProbabilityTheory Set

noncomputable def actualBoxQuadratureIntegrand
    (box : ProfileBox) (profile frequency : ℝ) : ℝ :=
  Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^ rows *
    (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))

theorem continuous_actualBoxQuadratureIntegrand
    (box : ProfileBox) (profile : ℝ) (hlam : 0 < (box.lam : ℝ))
    (hlamOne : (box.lam : ℝ) < 1) :
    Continuous (actualBoxQuadratureIntegrand box profile) := by
  have hbase : Continuous (fun frequency : ℝ ↦
      (1 : ℂ) - ((box.lam : ℂ) + (frequency : ℂ) * Complex.I)) := by
    fun_prop
  have hslit : ∀ frequency : ℝ,
      (1 : ℂ) - ((box.lam : ℂ) + (frequency : ℂ) * Complex.I) ∈
        Complex.slitPlane := by
    intro frequency
    rw [Complex.mem_slitPlane_iff]
    left
    simp
    linarith
  have hpowOne : Continuous (fun frequency : ℝ ↦
      ((1 : ℂ) - ((box.lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
        (-1 / 2 : ℂ)) :=
    hbase.cpow continuous_const hslit
  have hpowFive : Continuous (fun frequency : ℝ ↦
      ((1 : ℂ) - ((box.lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
        (-5 / 2 : ℂ)) :=
    hbase.cpow continuous_const hslit
  have hs : Continuous (fun frequency : ℝ ↦
      (box.lam : ℂ) + (frequency : ℂ) * Complex.I) := by fun_prop
  have hleading : Continuous (fun frequency : ℝ ↦
      ‖((1 : ℂ) - ((box.lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
          (-1 / 2 : ℂ) -
        ((profile / 8 : ℝ) : ℂ) *
          ((box.lam : ℂ) + (frequency : ℂ) * Complex.I) ^ 2 *
        ((1 : ℂ) - ((box.lam : ℂ) + (frequency : ℂ) * Complex.I)) ^
          (-5 / 2 : ℂ)‖) := by
    simpa only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, mul_assoc] using
      (hpowOne.sub
        ((continuous_const : Continuous fun _ : ℝ ↦ ((profile / 8 : ℝ) : ℂ)).mul
          ((hs.pow 2).mul hpowFive))).norm
  have hd8 : Continuous (fun frequency : ℝ ↦
      quadraticExpDerivativeMajorant 8
        ‖(box.lam : ℂ) + (frequency : ℂ) * Complex.I‖ (box.lam : ℝ)) := by
    unfold quadraticExpDerivativeMajorant
    fun_prop
  have hd6 : Continuous (fun frequency : ℝ ↦
      quadraticExpDerivativeMajorant 6
        ‖(box.lam : ℂ) + (frequency : ℂ) * Complex.I‖ (box.lam : ℝ)) := by
    unfold quadraticExpDerivativeMajorant
    fun_prop
  have hU4 : Continuous (fun frequency : ℝ ↦
      sparseUpperFourthOrderNormalizedMajorant profile (box.lam : ℝ) frequency) := by
    unfold sparseUpperFourthOrderNormalizedMajorant
    exact continuous_const.mul
      ((hleading.add (continuous_const.mul hd8)).add (continuous_const.mul hd6))
  have hrow : Continuous (fun frequency : ℝ ↦
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency) := by
    unfold sparseUpperContourRowMajorant
    exact hU4.min continuous_const
  have hsqrt : Continuous (fun frequency : ℝ ↦
      Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) := by fun_prop
  have hsqrtNe : ∀ frequency : ℝ,
      Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) ≠ 0 := by
    intro frequency
    positivity
  have hinverse : Continuous (fun frequency : ℝ ↦
      1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) := by
    exact continuous_const.div₀ hsqrt hsqrtNe
  unfold actualBoxQuadratureIntegrand
  exact ((by fun_prop : Continuous (fun frequency : ℝ ↦
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2))).mul
        (hrow.pow rows)).mul hinverse

/-- Literal upper-rectangle value encoded by `gaussianCell`. -/
noncomputable def gaussianCellRectangleValue
    (profileLeft profileRight lam sigma mesh : ℚ) (index : ℕ) : ℝ :=
  let frequencyLeft : ℚ := index * mesh
  let alpha : ℚ := sigma * sigma / 2
  (mesh : ℝ) * Real.exp (-(alpha * frequencyLeft * frequencyLeft : ℚ)) *
    gaussianCellRowUpperValue profileLeft profileRight lam mesh index ^ 512 *
    (1 / Real.sqrt ((lam * lam + frequencyLeft * frequencyLeft : ℚ) : ℝ))

noncomputable def boxRectangleChunkValue
    (box : ProfileBox) (start count : ℕ) : ℝ :=
  (List.range count).foldl
    (fun result offset ↦ result +
      gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) (start + offset)) 0

noncomputable def boxRectangleCellsValue (box : ProfileBox) : ℝ :=
  boxChunkPlan.foldl
    (fun result chunk ↦ result + boxRectangleChunkValue box chunk.1 chunk.2) 0

private theorem fold_plan_chunks_eq_covered_sum
    (plan : List (ℕ × ℕ)) (f : ℕ → ℝ) :
    plan.foldl (fun result chunk ↦ result +
      (List.range chunk.2).foldl
        (fun value offset ↦ value + f (chunk.1 + offset)) 0) 0 =
      ((UpperContourKernel.coveredCellsFor plan).map f).sum := by
  rw [Internal.foldl_add_eq_add_sum_map]
  simp only [zero_add]
  simp_rw [Internal.foldl_add_eq_add_sum_map, zero_add]
  have h := Internal.sum_map_sum_eq_sum_flatMap plan
    (fun chunk ↦ (List.range chunk.2).map (fun offset ↦ chunk.1 + offset)) f
  simpa only [List.map_map, Function.comp_def,
    UpperContourKernel.coveredCellsFor] using h

private theorem boxRectangleCellsValue_eq_sum (box : ProfileBox) :
    boxRectangleCellsValue box =
      ∑ i ∈ Finset.range 800,
        gaussianCellRectangleValue box.profileLeft box.profileRight
          box.lam box.sigma (1 / 100) i := by
  let f : ℕ → ℝ := fun i ↦
    gaussianCellRectangleValue box.profileLeft box.profileRight
      box.lam box.sigma (1 / 100) i
  rw [Internal.finset_sum_range_eq_list_sum_map]
  calc
    boxRectangleCellsValue box =
        ((UpperContourKernel.coveredCellsFor boxChunkPlan).map f).sum := by
      unfold boxRectangleCellsValue boxRectangleChunkValue
      exact fold_plan_chunks_eq_covered_sum boxChunkPlan f
    _ = ((List.range 800).map f).sum :=
      congrArg (fun xs : List ℕ ↦ (xs.map f).sum) boxChunkPlan_covers

private theorem boxComputedCells_contains_boxRectangleCells
    (box : ProfileBox)
    (hcell : ∀ i,
      (gaussianCell box.profileLeft box.profileRight box.lam box.sigma
        (1 / 100) i).Contains
      (gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) i)) :
    ((boxComputedChunks box).foldl (fun acc cell ↦ acc + cell)
      (UpperContourKernel.zero contourPrecision)).Contains
        (boxRectangleCellsValue box) := by
  have hzero : (UpperContourKernel.zero contourPrecision).Contains (0 : ℝ) := by
    simpa [UpperContourKernel.zero, UpperContourKernel.frac] using
      Interval.contains_ofRat contourPrecision (0 : ℚ)
  unfold boxComputedChunks boxRectangleCellsValue
  rw [List.foldl_map]
  apply Internal.contains_foldl_add boxChunkPlan
    (fun chunk ↦ boxCellChunk box chunk.1 chunk.2)
    (fun chunk ↦ boxRectangleChunkValue box chunk.1 chunk.2)
  · intro chunk _
    unfold boxCellChunk boxRectangleChunkValue
    apply Internal.contains_foldl_add (List.range chunk.2)
      (fun offset ↦ gaussianCell box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) (chunk.1 + offset))
      (fun offset ↦ gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) (chunk.1 + offset))
    · intro offset _
      exact hcell (chunk.1 + offset)
    · exact hzero
  · exact hzero

/-- Cellwise domination of the actual canonical row-majorant integrand by
the literal left-endpoint rectangle encoded by the producer. -/
theorem actualBoxQuadratureIntegrand_le_rectangle
    (box : ProfileBox) (profile frequency : ℝ) (index : ℕ)
    (hprofile : 0 ≤ profile) (hlam : 0 < (box.lam : ℝ))
    (hlamOne : (box.lam : ℝ) < 1)
    (hfrequency : ((((index : ℕ) : ℚ) / 100 : ℚ) : ℝ) ≤ frequency)
    (hrow : sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      gaussianCellRowUpperValue box.profileLeft box.profileRight
        box.lam (1 / 100) index) :
    (1 / 100 : ℝ) * actualBoxQuadratureIntegrand box profile frequency ≤
      gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) index := by
  let left : ℝ := ((((index : ℕ) : ℚ) / 100 : ℚ) : ℝ)
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
  change (1 / 100 : ℝ) *
      (Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
        sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^ rows *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) ≤ _
  calc
    _ = (1 / 100 : ℝ) *
        ((Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) *
          sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^ rows) := by ring
    _ ≤ (1 / 100 : ℝ) *
        ((Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * left ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + left ^ 2))) *
          gaussianCellRowUpperValue box.profileLeft box.profileRight
            box.lam (1 / 100) index ^ rows) :=
      mul_le_mul_of_nonneg_left hproduct (by norm_num)
    _ = _ := by
      dsimp only [left]
      push_cast
      norm_num [rows]
      ring

theorem integrable_actualBoxQuadratureIntegrand
    (box : ProfileBox) (profile : ℝ) (hprofile : 0 ≤ profile)
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1)
    (hsigma : 0 < (box.sigma : ℝ)) :
    Integrable (actualBoxQuadratureIntegrand box profile) := by
  let cap := realRowDeficitCap
    (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))
  let dominating : ℝ → ℝ := fun frequency ↦
    (cap ^ rows / (box.lam : ℝ)) *
      Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2)
  have hdominating : Integrable dominating := by
    exact (integrable_exp_neg_mul_sq (by positivity : 0 < (box.sigma : ℝ) ^ 2 / 2)).const_mul _
  apply hdominating.mono'
    (continuous_actualBoxQuadratureIntegrand box profile hlam hlamOne).aestronglyMeasurable
  filter_upwards [] with frequency
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · have hrowNonneg := sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne
    have hrowCap : sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        cap := min_le_right _ _
    have hpower := pow_le_pow_left₀ hrowNonneg hrowCap rows
    have hsqrt : (box.lam : ℝ) ≤
        Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) := by
      exact (Real.le_sqrt hlam.le (by positivity)).2 (by nlinarith [sq_nonneg frequency])
    have hinverse : 1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) ≤
        1 / (box.lam : ℝ) := one_div_le_one_div_of_le hlam hsqrt
    have hcapNonneg : 0 ≤ cap := Internal.realRowDeficitCap_nonneg (by positivity)
    unfold actualBoxQuadratureIntegrand dominating
    dsimp only [cap]
    calc
      _ ≤ Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          cap ^ rows * (1 / (box.lam : ℝ)) := by gcongr
      _ = _ := by ring
  · unfold actualBoxQuadratureIntegrand
    positivity [sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne]

/-- The first `n` mesh cells dominate the actual canonical integrand on
`(0,n/100]`. This generic induction is the semantic 800-cell summation. -/
theorem integral_Ioc_actualBoxQuadratureIntegrand_le_sum_rectangles
    (box : ProfileBox) (profile : ℝ) (n : ℕ)
    (hprofile : 0 ≤ profile) (hlam : 0 < (box.lam : ℝ))
    (hlamOne : (box.lam : ℝ) < 1)
    (hrow : ∀ i < n, ∀ frequency ∈
      Set.Ioc ((i : ℝ) / 100) (((i + 1 : ℕ) : ℝ) / 100),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue box.profileLeft box.profileRight
          box.lam (1 / 100) i) :
    (∫ frequency : ℝ in Set.Ioc 0 ((n : ℝ) / 100),
      actualBoxQuadratureIntegrand box profile frequency) ≤
      ∑ i ∈ Finset.range n,
        gaussianCellRectangleValue box.profileLeft box.profileRight
          box.lam box.sigma (1 / 100) i := by
  have hcontinuous := continuous_actualBoxQuadratureIntegrand
    box profile hlam hlamOne
  induction n with
  | zero => simp
  | succ n ih =>
      have hrowPrevious : ∀ i < n, ∀ frequency ∈
          Set.Ioc ((i : ℝ) / 100) (((i + 1 : ℕ) : ℝ) / 100),
          sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
            gaussianCellRowUpperValue box.profileLeft box.profileRight
              box.lam (1 / 100) i := by
        intro i hi
        exact hrow i (hi.trans n.lt_succ_self)
      have hprevious := ih hrowPrevious
      let left : ℝ := (n : ℝ) / 100
      let right : ℝ := ((n + 1 : ℕ) : ℝ) / 100
      let rectangle := gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) n
      have hleftRight : left ≤ right := by
        dsimp only [left, right]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast n.le_succ
        · norm_num
      have hcellPointwise : ∀ frequency ∈ Set.Ioc left right,
          actualBoxQuadratureIntegrand box profile frequency ≤
            rectangle / (1 / 100 : ℝ) := by
        intro frequency hfrequency
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 100)).2
        dsimp only [left, right, rectangle] at hfrequency ⊢
        have hfrequencyLeft :
            (((((n : ℕ) : ℚ) / 100 : ℚ) : ℝ)) ≤ frequency := by
          push_cast
          exact hfrequency.1.le
        simpa only [mul_comm] using
          actualBoxQuadratureIntegrand_le_rectangle box profile frequency n
            hprofile hlam hlamOne hfrequencyLeft
            (hrow n n.lt_succ_self frequency hfrequency)
      have hcell :
          (∫ frequency : ℝ in Set.Ioc left right,
            actualBoxQuadratureIntegrand box profile frequency) ≤ rectangle := by
        calc
          _ ≤ ∫ _frequency : ℝ in Set.Ioc left right,
              rectangle / (1 / 100 : ℝ) := by
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
      have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) left) (Set.Ioc left right) := by
        exact Set.disjoint_left.2 fun x hx hy ↦ (not_lt_of_ge hx.2) hy.1
      have hunion : Set.Ioc (0 : ℝ) left ∪ Set.Ioc left right =
          Set.Ioc 0 right := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc]
        constructor
        · rintro (hx | hx)
          · exact ⟨hx.1, hx.2.trans hleftRight⟩
          · exact ⟨lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ left) hx.1, hx.2⟩
        · intro hx
          by_cases hxl : x ≤ left
          · exact Or.inl ⟨hx.1, hxl⟩
          · exact Or.inr ⟨lt_of_not_ge hxl, hx.2⟩
      rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioc
        (hcontinuous.integrableOn_Ioc) (hcontinuous.integrableOn_Ioc)]
      rw [Finset.sum_range_succ]
      exact add_le_add hprevious hcell

/-- A Gaussian cell encloses the literal upper rectangle it encodes. -/
theorem gaussianCell_contains_rectangle
    (profileLeft profileRight lam sigma mesh : ℚ) (index : ℕ)
    (hrowUpper : 0 ≤
      (min (realCapUpper contourPrecision profileLeft lam).hi
        (max
          (rowExpressionOnCell profileLeft (index * mesh) ((index + 1) * mesh) lam).hi
          (rowExpressionOnCell profileRight (index * mesh) ((index + 1) * mesh) lam).hi)))
    (hbase : 0 ≤
      (UpperContourKernel.frac contourPrecision
        (lam * lam + (index * mesh) * (index * mesh))).lo)
    (hsqrt : 0 <
      (UpperContourKernel.frac contourPrecision
        (lam * lam + (index * mesh) * (index * mesh))).sqrt.lo) :
    (gaussianCell profileLeft profileRight lam sigma mesh index).Contains
      (gaussianCellRectangleValue profileLeft profileRight lam sigma mesh index) := by
  let frequencyLeft : ℚ := index * mesh
  let alpha : ℚ := sigma * sigma / 2
  let rowUpper := min (realCapUpper contourPrecision profileLeft lam).hi
    (max
      (rowExpressionOnCell profileLeft frequencyLeft ((index + 1) * mesh) lam).hi
      (rowExpressionOnCell profileRight frequencyLeft ((index + 1) * mesh) lam).hi)
  have hmeshI := Interval.contains_ofRat contourPrecision mesh
  have hexp := Exp.negUpper_contains (p := contourPrecision) (k := 24)
    (x := alpha * frequencyLeft * frequencyLeft) (by
      dsimp only [alpha, frequencyLeft]
      have hsigmaSq : 0 ≤ sigma * sigma := mul_self_nonneg sigma
      have hfrequencySq : 0 ≤ (index * mesh) * (index * mesh) :=
        mul_self_nonneg _
      calc
        0 ≤ (sigma * sigma / 2) * ((index * mesh) * (index * mesh)) :=
          mul_nonneg (div_nonneg hsigmaSq (by norm_num)) hfrequencySq
        _ = (sigma * sigma / 2) * (index * mesh) * (index * mesh) := by ring)
  have hrow : (Interval.mk 0 rowUpper : Interval contourPrecision).Contains
      (Dyadic.toReal contourPrecision rowUpper) := by
    constructor
    · simp only [Dyadic.toReal_zero]
      simpa using Internal.toReal_mono (p := contourPrecision) hrowUpper
    · rfl
  have hrowPower := Interval.contains_squareN hrow 9
  have hbaseI :
      (UpperContourKernel.frac contourPrecision
        (lam * lam + frequencyLeft * frequencyLeft)).Contains
      ((lam * lam + frequencyLeft * frequencyLeft : ℚ) : ℝ) :=
    Interval.contains_ofRat contourPrecision _
  have hsqrtI := Interval.contains_sqrt hbase hbaseI
  have hinverse :
      (UpperContourKernel.inverseSqrtAtLeft contourPrecision frequencyLeft lam).Contains
        (1 / Real.sqrt
          ((lam * lam + frequencyLeft * frequencyLeft : ℚ) : ℝ)) := by
    simpa [UpperContourKernel.inverseSqrtAtLeft, div_eq_mul_inv] using
      Interval.contains_reciprocal_of_pos hsqrt hsqrtI
  have hproduct := Interval.contains_mul
    (Interval.contains_mul (Interval.contains_mul hmeshI hexp) hrowPower) hinverse
  simpa [gaussianCell, gaussianCellRectangleValue, gaussianCellRowUpperValue,
    frequencyLeft, alpha, rowUpper, UpperContourKernel.frac,
    Interval.iterSquare_eq_pow_two_pow] using hproduct

/-- Literal tail value encoded after the 800 cells of one box. -/
noncomputable def boxTailValue (box : ProfileBox) (profile : ℝ) : ℝ :=
  let cutoff : ℚ := 8
  let alpha : ℚ := box.sigma * box.sigma / 2
  realRowDeficitCap
      (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))) ^ 512 *
    Real.exp (-(alpha * cutoff * cutoff : ℚ)) *
    ((1 / (2 * (alpha * cutoff * cutoff)) : ℚ) : ℝ)

/-- The producer's literal tail value majorizes the actual canonical
row-majorant integrand beyond frequency eight. -/
theorem integral_Ioi_actualBoxQuadratureIntegrand_le_boxTailValue
    (box : ProfileBox) (profile : ℝ) (hprofile : 0 ≤ profile)
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1)
    (hsigma : 0 < (box.sigma : ℝ)) :
    (∫ frequency : ℝ in Set.Ioi 8,
      actualBoxQuadratureIntegrand box profile frequency) ≤
        boxTailValue box profile := by
  let cap := realRowDeficitCap
    (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))
  let upper : ℝ → ℝ := fun frequency ↦
    cap ^ rows * Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
      (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))
  have hcapNonneg : 0 ≤ cap := Internal.realRowDeficitCap_nonneg (by positivity)
  have hupperMeasurable : AEStronglyMeasurable upper := by
    apply Measurable.aestronglyMeasurable
    dsimp only [upper]
    fun_prop
  have hupperIntegrable : IntegrableOn upper (Set.Ioi 8) := by
    let dominating : ℝ → ℝ := fun frequency ↦
      (cap ^ rows / (box.lam : ℝ)) *
        Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2)
    have hdominating : Integrable dominating :=
      (integrable_exp_neg_mul_sq
        (by positivity : 0 < (box.sigma : ℝ) ^ 2 / 2)).const_mul _
    apply hdominating.integrableOn.mono' hupperMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with frequency hfrequency
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hsqrt : (box.lam : ℝ) ≤
          Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) :=
        (Real.le_sqrt hlam.le (by positivity)).2 (by nlinarith [sq_nonneg frequency])
      have hinverse := one_div_le_one_div_of_le hlam hsqrt
      dsimp only [upper, dominating]
      calc
        _ ≤ cap ^ rows * Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
            (1 / (box.lam : ℝ)) := by gcongr
        _ = _ := by ring
    · dsimp only [upper]
      positivity
  have hactualIntegrable : IntegrableOn
      (actualBoxQuadratureIntegrand box profile) (Set.Ioi 8) :=
    (integrable_actualBoxQuadratureIntegrand box profile hprofile hlam hlamOne hsigma).integrableOn
  have hpointwise : ∀ frequency ∈ Set.Ioi (8 : ℝ),
      actualBoxQuadratureIntegrand box profile frequency ≤ upper frequency := by
    intro frequency _
    have hrowNonneg := sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne
    have hrowCap : sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        cap := min_le_right _ _
    have hpower := pow_le_pow_left₀ hrowNonneg hrowCap rows
    unfold actualBoxQuadratureIntegrand
    dsimp only [upper]
    calc
      _ ≤ Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          cap ^ rows * (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpower (Real.exp_nonneg _)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ frequency : ℝ in Set.Ioi 8, upper frequency :=
      setIntegral_mono_on hactualIntegrable hupperIntegrable measurableSet_Ioi hpointwise
    _ ≤ cap ^ rows * Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * (8 : ℝ) ^ 2) /
        (2 * ((box.sigma : ℝ) ^ 2 / 2) * (8 : ℝ) ^ 2) := by
      exact _root_.CertifiedJL.integral_Ioi_gaussianQuadratureWeight_le
        (halpha := by positivity) hlam (by norm_num) (pow_nonneg hcapNonneg rows)
    _ = boxTailValue box profile := by
      unfold boxTailValue
      dsimp only [cap]
      push_cast
      norm_num [rows]
      ring

/-- Once the U8 cap is semantically enclosed, the executable tail encloses
the literal Gaussian-tail rectangle used by the certificate. -/
theorem boxTail_contains
    (box : ProfileBox) (profile : ℝ)
    (hcap : (realCapUpper contourPrecision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    ((realCapUpper contourPrecision box.profileLeft box.lam).squareN 9 *
      Exp.negUpper contourPrecision
        ((box.sigma * box.sigma / 2) * 8 * 8) 28 *
      UpperContourKernel.frac contourPrecision
        (1 / (2 * ((box.sigma * box.sigma / 2) * 8 * 8)))).Contains
      (boxTailValue box profile) := by
  have hcapPower := Interval.contains_squareN hcap 9
  have hexp := Exp.negUpper_contains (p := contourPrecision) (k := 28)
    (x := (box.sigma * box.sigma / 2) * 8 * 8) (by
      have hsigmaSq : 0 ≤ box.sigma * box.sigma := mul_self_nonneg box.sigma
      positivity)
  have hfactor := Interval.contains_ofRat contourPrecision
    (1 / (2 * ((box.sigma * box.sigma / 2) * 8 * 8)) : ℚ)
  have hproduct := Interval.contains_mul
    (Interval.contains_mul hcapPower hexp) hfactor
  simpa [boxTailValue, UpperContourKernel.frac,
    Interval.iterSquare_eq_pow_two_pow] using hproduct

/-- The executable integral encloses the exact rectangle sum plus its literal
tail surrogate. This theorem consumes the producer's cells directly. -/
theorem boxIntegral_contains_rectangleCells_add_tail
    (box : ProfileBox) (profile : ℝ)
    (hcell : ∀ i,
      (gaussianCell box.profileLeft box.profileRight box.lam box.sigma
        (1 / 100) i).Contains
      (gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) i))
    (hcap : (realCapUpper contourPrecision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    (boxIntegral box).Contains
      (boxRectangleCellsValue box + boxTailValue box profile) := by
  have hcells := boxComputedCells_contains_boxRectangleCells box hcell
  have htail := boxTail_contains box profile hcap
  unfold boxIntegral boxIntegralFrom
  dsimp only
  exact Interval.contains_add hcells htail

/-- The 800 finite rectangles and the encoded Gaussian tail dominate the
actual positive-frequency canonical U4/U8 integrand. -/
theorem integral_Ioi_zero_actualBoxQuadratureIntegrand_le
    (box : ProfileBox) (profile : ℝ)
    (hprofile : 0 ≤ profile) (hlam : 0 < (box.lam : ℝ))
    (hlamOne : (box.lam : ℝ) < 1) (hsigma : 0 < (box.sigma : ℝ))
    (hrow : ∀ (i : ℕ), i < 800 → ∀ frequency ∈
      Set.Ioc ((i : ℝ) / 100) (((i + 1 : ℕ) : ℝ) / 100),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue box.profileLeft box.profileRight
          box.lam (1 / 100) i) :
    (∫ frequency : ℝ in Set.Ioi 0,
      actualBoxQuadratureIntegrand box profile frequency) ≤
        boxRectangleCellsValue box + boxTailValue box profile := by
  have hint := integrable_actualBoxQuadratureIntegrand
    box profile hprofile hlam hlamOne hsigma
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) 8) (Set.Ioi 8) := by
    exact Set.disjoint_left.2 fun x hx hy ↦ (not_lt_of_ge hx.2) hy
  have hunion : Set.Ioc (0 : ℝ) 8 ∪ Set.Ioi 8 = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · linarith
    · intro hx
      by_cases hx8 : x ≤ 8
      · exact Or.inl ⟨hx, hx8⟩
      · exact Or.inr (lt_of_not_ge hx8)
  have hcells := integral_Ioc_actualBoxQuadratureIntegrand_le_sum_rectangles
    box profile 800 hprofile hlam hlamOne hrow
  have htail := integral_Ioi_actualBoxQuadratureIntegrand_le_boxTailValue
    box profile hprofile hlam hlamOne hsigma
  rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioi
    hint.integrableOn hint.integrableOn]
  rw [show ((800 : ℕ) : ℝ) / 100 = 8 by norm_num] at hcells
  rw [← boxRectangleCellsValue_eq_sum box] at hcells
  exact add_le_add hcells htail

/-- Literal rational-prefactor value encoded by one low-profile box. The
separate analytic bridge from `314159/100000` and `phiLower` to `pi` and
`standardGaussianCDF` remains explicit at the trust boundary. -/
noncomputable def boxRationalPrefactorValue (box : ProfileBox) : ℝ :=
  let exponent := box.lam * (threshold - box.theta * box.sigma) -
    box.sigma * box.sigma * box.lam * box.lam / 2
  (2 ^ securityBits : ℝ) * ((1 / (314159 / 100000) : ℚ) : ℝ) *
    ((1 / UpperContourKernel.phiLower box.theta : ℚ) : ℝ) *
    Real.exp (-(exponent : ℚ)) *
    ((1 / (1 - box.lam) ^ (rows / 2) : ℚ) : ℝ)

/-- The certificate's rational reciprocal factors majorize the actual
`pi` and Gaussian-CDF reciprocals with the correct positive directions. -/
theorem boxActualPrefactorValue_le_rationalValue
    {box : ProfileBox} (hbox : box ∈ profileBoxes) :
    boxActualPrefactorValue box ≤ boxRationalPrefactorValue box := by
  obtain ⟨htheta, hthetaUpper, hphi, hlam, hlamOne, hsigma, hexponent, htarget⟩ :=
    profileBox_numeric_facts hbox
  have hpiPos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpiLowerPos : (0 : ℝ) < 314159 / 100000 := by norm_num
  have hpiInv : 1 / Real.pi ≤ (((1 / (314159 / 100000) : ℚ) : ℝ)) := by
    norm_num only [one_div, Rat.cast_inv, Rat.cast_ofScientific,
      Rat.cast_natCast]
    rw [show (100000 : ℝ) / 314159 =
      ((314159 : ℝ) / 100000)⁻¹ by norm_num]
    exact (inv_le_inv₀ hpiPos hpiLowerPos).2 piLower_lt_pi.le
  have hphiReal : (0 : ℝ) <
      ((UpperContourKernel.phiLower box.theta : ℚ) : ℝ) := by
    exact_mod_cast hphi
  have hCDFPos : 0 < standardGaussianCDF (box.theta : ℝ) :=
    standardGaussianCDF_pos _
  have hphiLe :
      ((UpperContourKernel.phiLower box.theta : ℚ) : ℝ) ≤
        standardGaussianCDF (box.theta : ℝ) :=
    phiLower_le_standardGaussianCDF box.theta htheta hthetaUpper
  have hphiInv : 1 / standardGaussianCDF (box.theta : ℝ) ≤
      (((1 / UpperContourKernel.phiLower box.theta : ℚ) : ℝ)) := by
    norm_num only [one_div, Rat.cast_inv]
    exact (inv_le_inv₀ hCDFPos hphiReal).2 hphiLe
  let exponent := box.lam * (threshold - box.theta * box.sigma) -
    box.sigma * box.sigma * box.lam * box.lam / 2
  have hscale : (0 : ℝ) ≤ 2 ^ securityBits := by positivity
  have hpiRational : (0 : ℝ) ≤
      (((1 / (314159 / 100000) : ℚ) : ℝ)) := by positivity
  have hCDFInv : 0 ≤ 1 / standardGaussianCDF (box.theta : ℝ) := by
    positivity
  have hexpReal : 0 ≤ Real.exp (-(exponent : ℚ)) := Real.exp_nonneg _
  have hgaussian : (0 : ℝ) ≤
      (((1 / (1 - box.lam) ^ (rows / 2) : ℚ) : ℝ)) := by positivity
  change
    (2 ^ securityBits : ℝ) * (1 / Real.pi) *
        (1 / standardGaussianCDF (box.theta : ℝ)) *
        Real.exp (-(exponent : ℚ)) *
        (((1 / (1 - box.lam) ^ (rows / 2) : ℚ) : ℝ)) ≤ _
  change _ ≤
    (2 ^ securityBits : ℝ) * (((1 / (314159 / 100000) : ℚ) : ℝ)) *
        (((1 / UpperContourKernel.phiLower box.theta : ℚ) : ℝ)) *
        Real.exp (-(exponent : ℚ)) *
        (((1 / (1 - box.lam) ^ (rows / 2) : ℚ) : ℝ))
  calc
    _ ≤ (2 ^ securityBits : ℝ) *
        (((1 / (314159 / 100000) : ℚ) : ℝ)) *
        (1 / standardGaussianCDF (box.theta : ℝ)) *
        Real.exp (-(exponent : ℚ)) *
        (((1 / (1 - box.lam) ^ (rows / 2) : ℚ) : ℝ)) := by
      gcongr
    _ ≤ _ := by
      gcongr

/-- The executable box prefactor encloses its literal rational surrogate. -/
theorem boxPrefactor_contains_rationalValue
    (box : ProfileBox)
    (hexponent : 0 ≤ box.lam * (threshold - box.theta * box.sigma) -
      box.sigma * box.sigma * box.lam * box.lam / 2) :
    (boxPrefactor box).Contains (boxRationalPrefactorValue box) := by
  have hscaledExponential := UpperContourKernel.scaledNegExpUpper_contains
    contourPrecision 12
      (box.lam * (threshold - box.theta * box.sigma) -
        box.sigma * box.sigma * box.lam * box.lam / 2) 32 4 hexponent
  have hpi := Interval.contains_ofRat contourPrecision
    (1 / (314159 / 100000) : ℚ)
  have hphi := Interval.contains_ofRat contourPrecision
    (1 / UpperContourKernel.phiLower box.theta : ℚ)
  have hgaussian := Interval.contains_ofRat contourPrecision
    (1 / (1 - box.lam) ^ (rows / 2) : ℚ)
  have hproduct := Interval.contains_mul
    (Interval.contains_mul
      (Interval.contains_mul hscaledExponential hpi) hphi) hgaussian
  simpa [boxPrefactor, boxRationalPrefactorValue, securityBits,
    UpperContourKernel.frac, mul_assoc, mul_left_comm, mul_comm] using hproduct

/-- Generic low-box endpoint consumer. A semantic quadrature proof supplies
`hintegral`; the checked rational endpoint then gives the strict target. -/
theorem lowBoxEndpoint_lt_target
    (box : ProfileBox) (integralValue : ℝ)
    (hexponent : 0 ≤ box.lam * (threshold - box.theta * box.sigma) -
      box.sigma * box.sigma * box.lam * box.lam / 2)
    (hintegral : (boxIntegral box).Contains integralValue)
    (hverified : (boxBound box).upperRat < box.target) :
    boxRationalPrefactorValue box * integralValue < (box.target : ℝ) := by
  have hprefactor := boxPrefactor_contains_rationalValue box hexponent
  have hbound : (boxBound box).Contains
      (boxRationalPrefactorValue box * integralValue) := by
    simpa [boxBound] using Interval.contains_mul hprefactor hintegral
  have hupper : boxRationalPrefactorValue box * integralValue ≤
      ((boxBound box).upperRat : ℝ) := by
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using hbound.2
  have hverifiedReal : ((boxBound box).upperRat : ℝ) < (box.target : ℝ) := by
    exact_mod_cast hverified
  exact hupper.trans_lt hverifiedReal

/-- Consumer-ready analytic endpoint for one generated low-profile box. The
premises are the local cell/cap soundness obligations; the conclusion is the
actual positive-contour integral with the true `pi` and Gaussian CDF. -/
theorem actualLowBoxEndpoint_lt_target
    {box : ProfileBox} (hbox : box ∈ profileBoxes) (profile : ℝ)
    (hprofile : 0 ≤ profile)
    (hcell : ∀ i,
      (gaussianCell box.profileLeft box.profileRight box.lam box.sigma
        (1 / 100) i).Contains
      (gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) i))
    (hcap : (realCapUpper contourPrecision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))))
    (hrow : ∀ (i : ℕ), i < 800 → ∀ frequency ∈
      Set.Ioc ((i : ℝ) / 100) (((i + 1 : ℕ) : ℝ) / 100),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue box.profileLeft box.profileRight
          box.lam (1 / 100) i)
    (hverified : (boxBound box).upperRat < box.target) :
    boxActualPrefactorValue box *
        (∫ frequency : ℝ in Set.Ioi 0,
          actualBoxQuadratureIntegrand box profile frequency) <
      (box.target : ℝ) := by
  obtain ⟨_, _, _, hlamRat, hlamOneRat, hsigmaRat, hexponent, _⟩ :=
    profileBox_numeric_facts hbox
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast hlamRat
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast hlamOneRat
  have hsigma : 0 < (box.sigma : ℝ) := by exact_mod_cast hsigmaRat
  let integralValue := ∫ frequency : ℝ in Set.Ioi 0,
    actualBoxQuadratureIntegrand box profile frequency
  let surrogate := boxRectangleCellsValue box + boxTailValue box profile
  have hintegralLe : integralValue ≤ surrogate := by
    exact integral_Ioi_zero_actualBoxQuadratureIntegrand_le
      box profile hprofile hlam hlamOne hsigma hrow
  have hintegralNonneg : 0 ≤ integralValue := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    unfold actualBoxQuadratureIntegrand
    positivity [sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne]
  have hsurrogateNonneg : 0 ≤ surrogate := hintegralNonneg.trans hintegralLe
  have hprefactorLe := boxActualPrefactorValue_le_rationalValue hbox
  have hrationalNonneg : 0 ≤ boxRationalPrefactorValue box := by
    unfold boxRationalPrefactorValue
    dsimp only
    push_cast
    positivity
  have hproduct : boxActualPrefactorValue box * integralValue ≤
      boxRationalPrefactorValue box * surrogate :=
    mul_le_mul hprefactorLe hintegralLe hintegralNonneg hrationalNonneg
  have hintegralContains : (boxIntegral box).Contains surrogate := by
    exact boxIntegral_contains_rectangleCells_add_tail box profile hcell hcap
  exact hproduct.trans_lt
    (lowBoxEndpoint_lt_target box surrogate hexponent hintegralContains hverified)

/-- Exact U10/U4 reduction into the positive-frequency integrand consumed by
one profile box. -/
theorem scaled_realProjectionSqNorm_toReal_le_actualBoxEndpoint
    {d : ℕ} (a : Fin d → ℝ) (box : ProfileBox)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hfourth : ∀ frequency : ℝ,
      Real.sqrt (1 - (box.lam : ℝ)) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a) (box.lam : ℝ) frequency)
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1)
    (hsigma : 0 < (box.sigma : ℝ)) :
    (2 ^ securityBits : ℝ) *
        (eventProbability (sparseRademacherMatrix rows d)
          (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal ≤
      boxActualPrefactorValue box *
        (∫ frequency : ℝ in Set.Ioi 0,
          actualBoxQuadratureIntegrand box (sparseProfileFourthMoment a) frequency) := by
  let contour : ℝ → ℝ := fun frequency =>
    ‖shiftedGaussianContourWeight (box.sigma : ℝ) (box.theta : ℝ)
      (threshold : ℝ) (box.lam : ℝ) frequency‖ *
      ‖quadraticComplexMGF
        (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure
        ((box.lam : ℝ) + frequency * Complex.I) ^ rows‖
  let coefficient : ℝ :=
    (1 / (2 * Real.pi * standardGaussianCDF (box.theta : ℝ))) *
      Real.exp (-((box.lam : ℝ) * ((threshold : ℝ) -
        (box.theta : ℝ) * (box.sigma : ℝ)) -
          (box.sigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
      (1 / Real.sqrt (1 - (box.lam : ℝ))) ^ rows
  have hpointwise : ∀ frequency : ℝ, contour frequency ≤
      coefficient * actualBoxQuadratureIntegrand box
        (sparseProfileFourthMoment a) frequency := by
    intro frequency
    have hnormalized := normalized_rowMGF_le_contourRowMajorant
      a hlam.le hlamOne hnorm (hfourth frequency)
    have hsqrt : 0 < Real.sqrt (1 - (box.lam : ℝ)) :=
      Real.sqrt_pos.2 (sub_pos.mpr hlamOne)
    have hnormLe :
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure
          ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        (1 / Real.sqrt (1 - (box.lam : ℝ))) *
          sparseUpperContourRowMajorant
            (sparseProfileFourthMoment a) (box.lam : ℝ) frequency := by
      rw [one_div, inv_mul_eq_div]
      exact (le_div_iff₀ hsqrt).2 (by simpa [mul_comm] using hnormalized)
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hnormLe rows
    have hCDF : 0 < standardGaussianCDF (box.theta : ℝ) :=
      standardGaussianCDF_pos _
    have hden : 0 < Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2) := by
      positivity
    have hcommon : 0 ≤
        (1 / (2 * Real.pi * standardGaussianCDF (box.theta : ℝ))) *
          Real.exp (-((box.lam : ℝ) * ((threshold : ℝ) -
            (box.theta : ℝ) * (box.sigma : ℝ)) -
              (box.sigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
          Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) := by
      positivity
    dsimp only [contour, coefficient]
    rw [norm_shiftedGaussianContourWeight_eq_quadrature, norm_pow]
    unfold actualBoxQuadratureIntegrand
    calc
      _ ≤ (1 / (2 * Real.pi * standardGaussianCDF (box.theta : ℝ))) *
          Real.exp (-((box.lam : ℝ) * ((threshold : ℝ) -
            (box.theta : ℝ) * (box.sigma : ℝ)) -
              (box.sigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
          Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) *
          ((1 / Real.sqrt (1 - (box.lam : ℝ))) *
            sparseUpperContourRowMajorant
              (sparseProfileFourthMoment a) (box.lam : ℝ) frequency) ^ rows := by
        exact mul_le_mul_of_nonneg_left hpow hcommon
      _ = _ := by
        rw [mul_pow]
        ac_rfl
  have hcontour := sparseRademacherMatrix_realProjectionSqNorm_toReal_le_positiveContour
    (m := rows) a (sigma := (box.sigma : ℝ)) (theta := (box.theta : ℝ))
      (t := (threshold : ℝ)) (lambda := (box.lam : ℝ)) hsigma hlam
  have hcontourInt : Integrable contour :=
    integrable_sparseUpperContourNorm a rows hlam hsigma
  have hactualInt := integrable_actualBoxQuadratureIntegrand box
    (sparseProfileFourthMoment a) (by
      unfold sparseProfileFourthMoment
      positivity)
      hlam hlamOne hsigma
  have hintegral : (∫ frequency : ℝ in Set.Ioi 0, contour frequency) ≤
      coefficient * (∫ frequency : ℝ in Set.Ioi 0,
        actualBoxQuadratureIntegrand box (sparseProfileFourthMoment a) frequency) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hcontourInt.integrableOn
      (hactualInt.const_mul coefficient).integrableOn measurableSet_Ioi
      (fun frequency _ ↦ hpointwise frequency)
  have hevent :
      (eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal ≤
        2 * coefficient * (∫ frequency : ℝ in Set.Ioi 0,
          actualBoxQuadratureIntegrand box (sparseProfileFourthMoment a) frequency) := by
    calc
      _ ≤ 2 * (∫ frequency : ℝ in Set.Ioi 0, contour frequency) := by
        simpa only [contour] using hcontour
      _ ≤ 2 * (coefficient * (∫ frequency : ℝ in Set.Ioi 0,
          actualBoxQuadratureIntegrand box
            (sparseProfileFourthMoment a) frequency)) :=
        mul_le_mul_of_nonneg_left hintegral (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (2 ^ securityBits : ℝ) *
        (2 * coefficient * (∫ frequency : ℝ in Set.Ioi 0,
          actualBoxQuadratureIntegrand box (sparseProfileFourthMoment a) frequency)) :=
      mul_le_mul_of_nonneg_left hevent (by positivity)
    _ = _ := by
      have hsqrtSq : Real.sqrt (1 - (box.lam : ℝ)) ^ 2 =
          1 - (box.lam : ℝ) := Real.sq_sqrt (sub_nonneg.mpr hlamOne.le)
      have hpow : (1 / Real.sqrt (1 - (box.lam : ℝ))) ^ rows =
          (1 / (1 - (box.lam : ℝ))) ^ (rows / 2) := by
        calc
          _ = ((1 / Real.sqrt (1 - (box.lam : ℝ))) ^ 2) ^ 256 := by
            simpa [rows] using pow_mul
              (1 / Real.sqrt (1 - (box.lam : ℝ))) 2 256
          _ = (1 / (1 - (box.lam : ℝ))) ^ 256 := by
            rw [div_pow, one_pow, hsqrtSq]
          _ = _ := by norm_num [rows]
      unfold boxActualPrefactorValue
      dsimp only [coefficient]
      rw [hpow]
      push_cast
      simp only [securityBits, rows]
      -- Keep the 256th power factored: ring would otherwise expand its binomial.
      generalize (1 - (box.lam : ℝ)) = base
      ring

/-- The generated ten-box manifest covers the complete low-profile range. -/
theorem exists_profileBox_mem_and_contains
    {profile : ℝ} (hprofile0 : 0 ≤ profile)
    (hprofile20 : profile ≤ 1 / 20) :
    ∃ box ∈ profileBoxes, (box.profileLeft : ℝ) ≤ profile ∧
      profile ≤ (box.profileRight : ℝ) := by
  by_cases h0 : profile ≤ 1 / 1024
  · exact ⟨profileBox 0, by norm_num [profileBox, firstBox, profileBoxes],
      by simpa [profileBox, firstBox, profileBoxes] using hprofile0,
      by simpa [profileBox, firstBox, profileBoxes] using h0⟩
  by_cases h1 : profile ≤ 1 / 512
  · exact ⟨profileBox 1, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h0).le,
      by simpa [profileBox, firstBox, profileBoxes] using h1⟩
  by_cases h2 : profile ≤ 3 / 1024
  · exact ⟨profileBox 2, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h1).le,
      by simpa [profileBox, firstBox, profileBoxes] using h2⟩
  by_cases h3 : profile ≤ 1 / 256
  · exact ⟨profileBox 3, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h2).le,
      by simpa [profileBox, firstBox, profileBoxes] using h3⟩
  by_cases h4 : profile ≤ 3 / 512
  · exact ⟨profileBox 4, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h3).le,
      by simpa [profileBox, firstBox, profileBoxes] using h4⟩
  by_cases h5 : profile ≤ 1 / 128
  · exact ⟨profileBox 5, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h4).le,
      by simpa [profileBox, firstBox, profileBoxes] using h5⟩
  by_cases h6 : profile ≤ 1 / 64
  · exact ⟨profileBox 6, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h5).le,
      by simpa [profileBox, firstBox, profileBoxes] using h6⟩
  by_cases h7 : profile ≤ 3 / 128
  · exact ⟨profileBox 7, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h6).le,
      by simpa [profileBox, firstBox, profileBoxes] using h7⟩
  by_cases h8 : profile ≤ 1 / 32
  · exact ⟨profileBox 8, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h7).le,
      by simpa [profileBox, firstBox, profileBoxes] using h8⟩
  · exact ⟨profileBox 9, by norm_num [profileBox, firstBox, profileBoxes],
      by norm_num [profileBox, firstBox, profileBoxes]; exact (lt_of_not_ge h8).le,
      by simpa [profileBox, firstBox, profileBoxes] using hprofile20⟩

/-- Final low-profile sparse upper-tail consumer. Numeric replay is supplied
only through its direct local cell, cap, and endpoint facts. -/
theorem sparseUpper_lowProfile
    {d : ℕ} (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : sparseProfileFourthMoment a ≤ 1 / 20)
    (hfourth : ∀ box ∈ profileBoxes, ∀ frequency : ℝ,
      Real.sqrt (1 - (box.lam : ℝ)) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a) (box.lam : ℝ) frequency)
    (hcell : ∀ box ∈ profileBoxes, ∀ i,
      (gaussianCell box.profileLeft box.profileRight box.lam box.sigma
        (1 / 100) i).Contains
      (gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) i))
    (hcap : ∀ box ∈ profileBoxes,
      (sparseProfileFourthMoment a) ∈
        Set.Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      (realCapUpper contourPrecision box.profileLeft box.lam).Contains
        (realRowDeficitCap (Real.sqrt (sparseProfileFourthMoment a) *
          (box.lam : ℝ) / (1 - (box.lam : ℝ)))))
    (hrow : ∀ box ∈ profileBoxes,
      (sparseProfileFourthMoment a) ∈
        Set.Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      ∀ (i : ℕ), i < 800 → ∀ frequency ∈
        Set.Ioc ((i : ℝ) / 100) (((i + 1 : ℕ) : ℝ) / 100),
        sparseUpperContourRowMajorant (sparseProfileFourthMoment a)
            (box.lam : ℝ) frequency ≤
          gaussianCellRowUpperValue box.profileLeft box.profileRight
            box.lam (1 / 100) i)
    (hverified : ∀ box ∈ profileBoxes,
      (boxBound box).upperRat < box.target) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J) <
      failureTarget securityBits := by
  have hprofile0 : 0 ≤ sparseProfileFourthMoment a := by
    unfold sparseProfileFourthMoment
    positivity
  obtain ⟨box, hbox, hleft, hright⟩ :=
    exists_profileBox_mem_and_contains hprofile0 hprofile
  have hmem : sparseProfileFourthMoment a ∈
      Set.Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) := ⟨hleft, hright⟩
  obtain ⟨_, _, _, hlamRat, hlamOneRat, hsigmaRat, _, htarget⟩ :=
    profileBox_numeric_facts hbox
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast hlamRat
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast hlamOneRat
  have hsigma : 0 < (box.sigma : ℝ) := by exact_mod_cast hsigmaRat
  have hscaled := scaled_realProjectionSqNorm_toReal_le_actualBoxEndpoint
    a box hnorm (hfourth box hbox) hlam hlamOne hsigma
  have hendpoint := actualLowBoxEndpoint_lt_target hbox
    (sparseProfileFourthMoment a) hprofile0 (hcell box hbox)
      (hcap box hbox hmem) (hrow box hbox hmem) (hverified box hbox)
  have hscaledOne : (2 ^ securityBits : ℝ) *
      (eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal < 1 :=
    hscaled.trans_lt (hendpoint.trans (by exact_mod_cast htarget))
  have hreal :
      (eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal <
        (2 : ℝ)⁻¹ ^ securityBits := by
    rw [inv_pow]
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ securityBits)).2
    simpa [mul_comm] using hscaledOne
  rw [← ENNReal.toReal_lt_toReal
    (by unfold eventProbability; exact PMF.apply_ne_top _ _)
    (by simp [failureTarget])]
  simpa [failureTarget] using hreal

end SparseUpperContour
end CertifiedJL
