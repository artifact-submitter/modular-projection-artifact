import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Numeric
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Final

open MeasureTheory Set
namespace CertifiedJL.SparseUpperContour.ShortTail

noncomputable def tailValue (box : ProfileBox) (profile : ℝ) (cutoff : ℚ) : ℝ :=
  let alpha : ℚ := box.sigma * box.sigma / 2
  realRowDeficitCap
      (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))) ^ 512 *
    Real.exp (-(alpha * cutoff * cutoff : ℚ)) *
    ((1 / (2 * (alpha * cutoff * cutoff)) : ℚ) : ℝ)

/-- The analytic Gaussian tail works at any positive rational cutoff. -/
theorem tail_integral_le
    (box : ProfileBox) (profile : ℝ) (cutoff : ℚ) (hcutoff : 0 < cutoff)
    (hprofile : 0 ≤ profile)
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1)
    (hsigma : 0 < (box.sigma : ℝ)) :
    (∫ frequency : ℝ in Set.Ioi (cutoff : ℝ),
      actualBoxQuadratureIntegrand box profile frequency) ≤
        tailValue box profile cutoff := by
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
  have hupperIntegrable : IntegrableOn upper (Set.Ioi (cutoff : ℝ)) := by
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
      (actualBoxQuadratureIntegrand box profile) (Set.Ioi (cutoff : ℝ)) :=
    (integrable_actualBoxQuadratureIntegrand box profile hprofile hlam hlamOne hsigma).integrableOn
  have hpointwise : ∀ frequency ∈ Set.Ioi ((cutoff : ℝ) : ℝ),
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
    _ ≤ ∫ frequency : ℝ in Set.Ioi (cutoff : ℝ), upper frequency :=
      setIntegral_mono_on hactualIntegrable hupperIntegrable measurableSet_Ioi hpointwise
    _ ≤ cap ^ rows * Real.exp (-((box.sigma : ℝ) ^ 2 / 2) * ((cutoff : ℝ) : ℝ) ^ 2) /
        (2 * ((box.sigma : ℝ) ^ 2 / 2) * ((cutoff : ℝ) : ℝ) ^ 2) := by
      exact _root_.CertifiedJL.integral_Ioi_gaussianQuadratureWeight_le
        (halpha := by positivity) hlam (by exact_mod_cast hcutoff) (pow_nonneg hcapNonneg rows)
    _ = tailValue box profile cutoff := by
      unfold tailValue
      dsimp only [cap]
      push_cast
      norm_num [rows]
      ring

noncomputable def rectangleCells (box : ProfileBox) (count : ℕ) : ℝ :=
  (plan count).foldl
    (fun result chunk => result + boxRectangleChunkValue box chunk.1 chunk.2) 0

theorem rectangleCells_eq_sum (box : ProfileBox) (count : ℕ)
    (hcoverage : UpperContourKernel.coveredCellsFor (plan count) =
      List.range (count * 25)) :
    rectangleCells box count = ∑ i ∈ Finset.range (count * 25),
      gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) i := by
  let f := gaussianCellRectangleValue box.profileLeft box.profileRight
    box.lam box.sigma (1 / 100)
  rw [Internal.finset_sum_range_eq_list_sum_map]
  change rectangleCells box count = ((List.range (count * 25)).map f).sum
  rw [← hcoverage]
  unfold rectangleCells boxRectangleChunkValue
  rw [Internal.foldl_add_eq_add_sum_map]
  simp only [zero_add]
  simp_rw [Internal.foldl_add_eq_add_sum_map, zero_add]
  have h := Internal.sum_map_sum_eq_sum_flatMap (plan count)
    (fun chunk => (List.range chunk.2).map (fun offset => chunk.1 + offset)) f
  simpa only [List.map_map, Function.comp_def, UpperContourKernel.coveredCellsFor] using h

theorem cells_contains (box : ProfileBox) (count : ℕ)
    (hcell : ∀ i,
      (gaussianCell box.profileLeft box.profileRight box.lam box.sigma (1 / 100) i).Contains
        (gaussianCellRectangleValue box.profileLeft box.profileRight
          box.lam box.sigma (1 / 100) i)) :
    ((computedChunks box count).foldl (· + ·)
      (UpperContourKernel.zero contourPrecision)).Contains (rectangleCells box count) := by
  have hzero : (UpperContourKernel.zero contourPrecision).Contains (0 : ℝ) := by
    simpa [UpperContourKernel.zero, UpperContourKernel.frac] using
      Interval.contains_ofRat contourPrecision (0 : ℚ)
  unfold computedChunks rectangleCells
  rw [List.foldl_map]
  apply Internal.contains_foldl_add (plan count)
    (fun chunk => boxCellChunk box chunk.1 chunk.2)
    (fun chunk => boxRectangleChunkValue box chunk.1 chunk.2)
  · intro chunk _
    unfold boxCellChunk boxRectangleChunkValue
    apply Internal.contains_foldl_add (List.range chunk.2)
      (fun offset => gaussianCell box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) (chunk.1 + offset))
      (fun offset => gaussianCellRectangleValue box.profileLeft box.profileRight
        box.lam box.sigma (1 / 100) (chunk.1 + offset))
    · intro offset _
      exact hcell (chunk.1 + offset)
    · exact hzero
  · exact hzero

theorem tail_contains (box : ProfileBox) (profile : ℝ) (cutoff : ℚ)
    (hcap : (realCapUpper contourPrecision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    ((realCapUpper contourPrecision box.profileLeft box.lam).squareN 9 *
      Exp.negUpper contourPrecision ((box.sigma * box.sigma / 2) * cutoff * cutoff) 28 *
      UpperContourKernel.frac contourPrecision
        (1 / (2 * ((box.sigma * box.sigma / 2) * cutoff * cutoff)))).Contains
      (tailValue box profile cutoff) := by
  have hx : 0 ≤ (box.sigma * box.sigma / 2) * cutoff * cutoff := by
    nlinarith [sq_nonneg (box.sigma * cutoff)]
  have hproduct := Interval.contains_mul
    (Interval.contains_mul (Interval.contains_squareN hcap 9)
      (Exp.negUpper_contains (p := contourPrecision) (k := 28) hx))
    (Interval.contains_ofRat contourPrecision
      (1 / (2 * ((box.sigma * box.sigma / 2) * cutoff * cutoff)) : ℚ))
  simpa [tailValue, UpperContourKernel.frac,
    Interval.iterSquare_eq_pow_two_pow] using hproduct

theorem integral_le (box : ProfileBox) (profile : ℝ) (count : ℕ)
    (hcount : 0 < count)
    (hcoverage : UpperContourKernel.coveredCellsFor (plan count) = List.range (count * 25))
    (hprofile : 0 ≤ profile) (hlam : 0 < (box.lam : ℝ))
    (hlamOne : (box.lam : ℝ) < 1) (hsigma : 0 < (box.sigma : ℝ))
    (hrow : ∀ i < count * 25, ∀ frequency ∈
      Set.Ioc ((i : ℝ) / 100) (((i + 1 : ℕ) : ℝ) / 100),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue box.profileLeft box.profileRight box.lam (1 / 100) i) :
    (∫ frequency : ℝ in Set.Ioi 0, actualBoxQuadratureIntegrand box profile frequency) ≤
      rectangleCells box count + tailValue box profile (count / 4) := by
  let cutoff : ℝ := count / 4
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  have hint := integrable_actualBoxQuadratureIntegrand box profile hprofile hlam hlamOne hsigma
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) cutoff) (Set.Ioi cutoff) :=
    Set.disjoint_left.2 fun _ hx hy => (not_lt_of_ge hx.2) hy
  have hunion : Set.Ioc (0 : ℝ) cutoff ∪ Set.Ioi cutoff = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · linarith
    · intro hx
      by_cases hxc : x ≤ cutoff
      · exact Or.inl ⟨hx, hxc⟩
      · exact Or.inr (lt_of_not_ge hxc)
  have hcells := integral_Ioc_actualBoxQuadratureIntegrand_le_sum_rectangles
    box profile (count * 25) hprofile hlam hlamOne hrow
  have htail := tail_integral_le box profile (count / 4) (by positivity)
    hprofile hlam hlamOne hsigma
  rw [← hunion, setIntegral_union hdisjoint measurableSet_Ioi
    hint.integrableOn hint.integrableOn]
  rw [rectangleCells_eq_sum box count hcoverage]
  have hn : ((count * 25 : ℕ) : ℝ) / 100 = cutoff := by
    dsimp [cutoff]
    push_cast
    ring
  have hc : (((count : ℚ) / 4 : ℚ) : ℝ) = cutoff := by simp [cutoff]
  rw [hn] at hcells
  rw [hc] at htail
  exact add_le_add hcells htail

/-- Soundness consumes proved prefix chunks and the original strict target.
The tail is analytic; it has no rectangle-certificate premise. -/
theorem endpoint_lt {box : ProfileBox} (hbox : box ∈ profileBoxes)
    (count : ℕ) (hcount : 0 < count)
    (hcoverage : UpperContourKernel.coveredCellsFor (plan count) = List.range (count * 25))
    (chunks : List (Interval contourPrecision))
    (hchunks : computedChunks box count = chunks)
    (hbudget : (boundFrom box count chunks).upperRat < box.target)
    {profile : ℝ} (hprofile : profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ)) :
    boxActualPrefactorValue box *
      (∫ frequency : ℝ in Ioi 0, actualBoxQuadratureIntegrand box profile frequency) <
        (box.target : ℝ) := by
  obtain ⟨_, _, _, hlamQ, hlamOneQ, hsigmaQ, hexponent, _⟩ :=
    profileBox_numeric_facts hbox
  have hleft : 0 ≤ (box.profileLeft : ℝ) := by
    simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
    rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hp : 0 ≤ profile := hleft.trans hprofile.1
  have hlam : 0 < (box.lam : ℝ) := by exact_mod_cast hlamQ
  have hlamOne : (box.lam : ℝ) < 1 := by exact_mod_cast hlamOneQ
  have hsigma : 0 < (box.sigma : ℝ) := by exact_mod_cast hsigmaQ
  have hbound := integral_le box profile count hcount hcoverage hp hlam hlamOne hsigma
    (fun i _ frequency hf =>
      profileBox_rowMajorant_le_gaussianCellRowUpperValue hbox hprofile i hf)
  have hcells := cells_contains box count
    (profileBox_gaussianCell_contains_rectangle hbox)
  rw [hchunks] at hcells
  have htail := tail_contains box profile (count / 4)
    (profileBox_realCapUpper_contains hbox hprofile)
  have hsum : (integralFrom box count chunks).Contains
      (rectangleCells box count + tailValue box profile (count / 4)) := by
    exact Interval.contains_add hcells htail
  have hproduct := Interval.contains_mul
    (boxPrefactor_contains_rationalValue box hexponent) hsum
  have hupper : boxRationalPrefactorValue box *
      (rectangleCells box count + tailValue box profile (count / 4)) ≤
      ((boundFrom box count chunks).upperRat : ℝ) := by
    simpa only [boundFrom, Interval.upperRat, Dyadic.cast_toRat] using hproduct.2
  have hinonneg : 0 ≤ ∫ frequency : ℝ in Ioi 0,
      actualBoxQuadratureIntegrand box profile frequency := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    unfold actualBoxQuadratureIntegrand
    positivity [sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hp hlam.le hlamOne]
  have hpref : 0 ≤ boxRationalPrefactorValue box := by
    unfold boxRationalPrefactorValue
    dsimp only
    push_cast
    positivity
  exact (mul_le_mul (boxActualPrefactorValue_le_rationalValue hbox) hbound
    hinonneg hpref).trans_lt (hupper.trans_lt (by exact_mod_cast hbudget))

end CertifiedJL.SparseUpperContour.ShortTail
