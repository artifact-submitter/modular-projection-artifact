import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.HermitePaper

/-!
# Producer canaries for the sparse Hermite interpolant

These tests use five asymmetric rational nodes.  In particular, the nodal
polynomial witnesses why checking only the ten node equations cannot replace
the zero normalization or the later universal majorization theorem.
-/

open scoped Polynomial

namespace CertifiedJL.Tests

open CertifiedJL Polynomial

noncomputable section

private def testNodes : Fin 5 → ℝ :=
  ![21 / 250, 303 / 1000, 581 / 1000, 417 / 500, 1961 / 2000]

private theorem testNodes_strictMono : StrictMono testNodes := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp [testNodes] <;> norm_num

private theorem testNodes_pos : 0 < testNodes 0 := by
  norm_num [testNodes]

private def testValues : Fin 5 → ℝ := ![2, 3, 5, 7, 11]

private def testSlopes : Fin 5 → ℝ := ![13, 17, 19, 23, 29]

/-- The paper nodes exercise unconditional interpolation uniqueness. -/
theorem hermite_paper_nodes_unique_canary (α : ℝ) :
    ∃! P, IsHermiteInterpolant α testNodes P :=
  existsUnique_isHermiteInterpolant testNodes_strictMono testNodes_pos

/-- The chosen normalization is pinned at the nonsampled endpoint zero. -/
theorem hermite_zero_endpoint_canary (α : ℝ) :
    (chosenHermiteInterpolant α testNodes).eval 0 = 0 :=
  chosenHermiteInterpolant_eval_zero α testNodes testNodes_strictMono testNodes_pos

/-- Self and off-diagonal branches of the value basis are directly pinned. -/
theorem hermite_value_basis_branches_canary :
    (hermiteValueBasis testNodes 2).eval (testNodes 2) = 1 ∧
      (hermiteValueBasis testNodes 2).eval (testNodes 4) = 0 := by
  constructor
  · simpa using hermiteValueBasis_eval testNodes_strictMono.injective 2 2
  · simpa using hermiteValueBasis_eval testNodes_strictMono.injective 2 4

/-- Self and off-diagonal branches of the slope basis are directly pinned. -/
theorem hermite_slope_basis_branches_canary :
    (hermiteSlopeBasis testNodes 1).derivative.eval (testNodes 1) = 1 ∧
      (hermiteSlopeBasis testNodes 1).derivative.eval (testNodes 3) = 0 ∧
      (hermiteSlopeBasis testNodes 1).eval (testNodes 4) = 0 := by
  constructor
  · simpa using hermiteSlopeBasis_derivative_eval testNodes_strictMono.injective 1 1
  · constructor
    · simpa using hermiteSlopeBasis_derivative_eval testNodes_strictMono.injective 1 3
    · exact hermiteSlopeBasis_eval 1 4

/-- Asymmetric values and slopes reject a swapped basis or node index. -/
theorem hermite_asymmetric_interpolant_canary :
    (hermiteInterpolant testNodes testValues testSlopes).eval (testNodes 2) = 5 ∧
      (hermiteInterpolant testNodes testValues testSlopes).derivative.eval (testNodes 3) = 23 := by
  constructor
  · simpa [testValues] using
      hermiteInterpolant_eval testNodes_strictMono.injective (value := testValues)
        (slope := testSlopes) 2
  · simpa [testSlopes] using
      hermiteInterpolant_derivative_eval testNodes_strictMono.injective (value := testValues)
        (slope := testSlopes) 3

/-- Node-only testing is insufficient: the nonzero nodal polynomial and its
derivative vanish at all five interpolation nodes. -/
theorem hermite_node_only_check_rejected :
    (∀ i, (hermiteNodal testNodes).eval (testNodes i) = 0) ∧
      (∀ i, (hermiteNodal testNodes).derivative.eval (testNodes i) = 0) ∧
      (hermiteNodal testNodes).eval 0 ≠ 0 := by
  refine ⟨hermiteNodal_eval_node testNodes,
    hermiteNodal_derivative_eval_node testNodes, ?_⟩
  apply hermiteNodal_eval_zero_ne
  intro i
  fin_cases i <;> norm_num [testNodes]

/-- The explicit construction and the chosen public interpolant agree. -/
theorem hermite_explicit_characterization_canary (α : ℝ) :
    chosenHermiteInterpolant α testNodes =
      hermiteZeroInterpolant testNodes (fun i ↦ (testNodes i).rpow α)
        (fun i ↦ α * (testNodes i).rpow (α - 1)) :=
  chosenHermiteInterpolant_eq_hermiteZeroInterpolant α testNodes

/-- Public degree, node-value, and node-slope equations are direct producer checks. -/
theorem chosen_hermite_interpolant_equations_canary (α : ℝ) :
    (chosenHermiteInterpolant α testNodes).natDegree ≤ 10 ∧
      (chosenHermiteInterpolant α testNodes).eval (testNodes 3) = (testNodes 3).rpow α ∧
      (chosenHermiteInterpolant α testNodes).derivative.eval (testNodes 1) =
        α * (testNodes 1).rpow (α - 1) := by
  exact ⟨chosenHermiteInterpolant_natDegree_le α testNodes testNodes_strictMono testNodes_pos,
    chosenHermiteInterpolant_eval_node α testNodes testNodes_strictMono testNodes_pos 3,
    chosenHermiteInterpolant_derivative_eval_node α testNodes testNodes_strictMono testNodes_pos 1⟩

/-- The exact derivative order and the sign at a concrete fractional exponent
are pinned independently of the future interval argument. -/
theorem hermite_rpow_eleven_sign_canary :
    (deriv^[11] (fun u : ℝ ↦ u.rpow (3 / 2 : ℝ))) 1 < 0 := by
  apply iter_deriv_rpow_eleven_neg
  <;> norm_num

/-- The remainder bridge pins the `7 + 5 = 12` multiplicity count that yields
an eleventh derivative zero at a positive point. -/
theorem hermite_repeated_rolle_multiplicity_canary
    (f : ℝ → ℝ) (s double : Finset ℝ) (hs : s.card = 7)
    (hdouble : double ⊆ s) (hdoubleCard : double.card = 5)
    (hpos : ∀ x ∈ s, 0 < x) (hzero : ∀ x ∈ s, f x = 0)
    (hdoubleZero : ∀ x ∈ double, deriv f x = 0)
    (hcont : ∀ k ≤ 11, ContinuousOn (deriv^[k] f) (Set.Ioi 0)) :
    ∃ c, 0 < c ∧ (deriv^[11] f) c = 0 :=
  exists_pos_iter_deriv_eleven_eq_zero_of_seven_zeros_five_double
    f s double hs hdouble hdoubleCard hpos hzero hdoubleZero hcont

/-- Universal majorization is pinned at the right endpoint, which is not an
interpolation node. -/
theorem hermite_right_endpoint_majorization_canary :
    (1 : ℝ).rpow (3 / 2 : ℝ) ≤
      (chosenHermiteInterpolant (3 / 2 : ℝ) testNodes).eval 1 := by
  apply chosenHermiteInterpolant_majorizes (t := testNodes)
  · norm_num
  · norm_num
  · exact testNodes_strictMono
  · exact testNodes_pos
  · simp [testNodes]
    norm_num
  · exact ⟨by norm_num, by norm_num⟩

/-- A nonsampled interior point rejects replacing the semantic theorem by
node-only testing. -/
theorem hermite_interior_majorization_canary :
    (1 / 2 : ℝ).rpow (3 / 2 : ℝ) ≤
      (chosenHermiteInterpolant (3 / 2 : ℝ) testNodes).eval (1 / 2) := by
  apply chosenHermiteInterpolant_majorizes (t := testNodes)
  · norm_num
  · norm_num
  · exact testNodes_strictMono
  · exact testNodes_pos
  · simp [testNodes]
    norm_num
  · constructor <;> norm_num

/-- The paper-node constants are pinned independently of the test-local
asymmetric data. -/
theorem sparse_hermite_nodes_canary :
    sparseHermiteNodes 0 = 21 / 250 ∧
      sparseHermiteNodes 1 = 303 / 1000 ∧
      sparseHermiteNodes 2 = 581 / 1000 ∧
      sparseHermiteNodes 3 = 417 / 500 ∧
      sparseHermiteNodes 4 = 1961 / 2000 ∧
      0 < sparseHermiteNodes 0 ∧ sparseHermiteNodes 4 < 1 := by
  simp [sparseHermiteNodes]
  norm_num

/-- The cosine substitution is directly exercised in its zero branch. -/
theorem hermite_zero_cosine_substitution_canary :
    (((0 : ℝ) ^ 2).rpow (3 / 2 : ℝ)) = |(0 : ℝ)|.rpow 3 := by
  exact sq_rpow_half_eq_abs_rpow (by norm_num)

/-- A negative, nonzero base pins the absolute-value normalization in the
square/rpow identity. -/
theorem hermite_negative_square_substitution_canary :
    (((-2 : ℝ) ^ 2).rpow (3 / 2 : ℝ)) = |(-2 : ℝ)|.rpow 3 := by
  exact sq_rpow_half_eq_abs_rpow (by norm_num)

/-- The main cosine transfer is consumed directly at a nonzero cosine. -/
theorem hermite_theta_zero_main_transfer_canary :
    |Real.cos 0|.rpow 3 ≤
      (chosenHermiteInterpolant (3 / 2) sparseHermiteNodes).eval
        ((Real.cos 0) ^ 2) := by
  exact abs_cos_rpow_le_sparseHermite (by norm_num) (by norm_num)

/-- A nonendpoint angle directly consumes the main paper transfer theorem. -/
theorem hermite_nonendpoint_main_transfer_canary :
    |Real.cos 1|.rpow 3 ≤
      (chosenHermiteInterpolant (3 / 2) sparseHermiteNodes).eval
        ((Real.cos 1) ^ 2) := by
  exact abs_cos_rpow_le_sparseHermite (by norm_num) (by norm_num)

/-- A concrete zero-cosine endpoint consumes the paper-node majorant. -/
theorem hermite_cos_pi_div_two_endpoint_canary :
    |Real.cos (Real.pi / 2)|.rpow 3 ≤
      (chosenHermiteInterpolant (3 / 2) sparseHermiteNodes).eval
        ((Real.cos (Real.pi / 2)) ^ 2) := by
  apply abs_cos_rpow_le_sparseHermite_of_cos_eq_zero
  · norm_num
  · norm_num
  · exact Real.cos_pi_div_two

end

end CertifiedJL.Tests
