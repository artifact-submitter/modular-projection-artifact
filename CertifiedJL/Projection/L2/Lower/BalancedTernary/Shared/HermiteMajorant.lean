import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Lagrange

/-!
# The five-node Hermite polynomial used by the sparse lower tail

This file isolates the semantic polynomial layer of the intermediate-row
argument.  The interpolant has degree at most ten, vanishes at zero, and
matches prescribed values and first derivatives at five distinct nodes.
-/

open scoped Polynomial

noncomputable section

namespace CertifiedJL

open Finset Polynomial

/-- The Lagrange cardinal polynomial for one of five nodes. -/
def hermiteLagrange (t : Fin 5 → ℝ) (i : Fin 5) : ℝ[X] :=
  Lagrange.basis Finset.univ t i

/-- The cardinal polynomial that selects a value and has zero slope at its node. -/
def hermiteValueBasis (t : Fin 5 → ℝ) (i : Fin 5) : ℝ[X] :=
  (1 - C (2 * (hermiteLagrange t i).derivative.eval (t i)) * (X - C (t i))) *
    (hermiteLagrange t i) ^ 2

/-- The cardinal polynomial that selects a slope and has zero value at its node. -/
def hermiteSlopeBasis (t : Fin 5 → ℝ) (i : Fin 5) : ℝ[X] :=
  (X - C (t i)) * (hermiteLagrange t i) ^ 2

/-- The ordinary degree-at-most-nine Hermite interpolant at five nodes. -/
def hermiteInterpolant (t value slope : Fin 5 → ℝ) : ℝ[X] :=
  ∑ i, C (value i) * hermiteValueBasis t i +
    ∑ i, C (slope i) * hermiteSlopeBasis t i

/-- The monic degree-ten polynomial with a double zero at every node. -/
def hermiteNodal (t : Fin 5 → ℝ) : ℝ[X] :=
  ∏ i, (X - C (t i)) ^ 2

/-- Correct the ordinary Hermite interpolant by its nodal polynomial.  The
result vanishes at zero when every node is nonzero. -/
def hermiteZeroInterpolant (t value slope : Fin 5 → ℝ) : ℝ[X] :=
  let Q := hermiteInterpolant t value slope
  Q - C (Q.eval 0 / (hermiteNodal t).eval 0) * hermiteNodal t

private theorem hermiteLagrange_eval_self {t : Fin 5 → ℝ} (ht : Function.Injective t)
    (i : Fin 5) : (hermiteLagrange t i).eval (t i) = 1 := by
  exact Lagrange.eval_basis_self ht.injOn (Finset.mem_univ i)

private theorem hermiteLagrange_eval_of_ne {t : Fin 5 → ℝ} {i j : Fin 5}
    (hij : i ≠ j) : (hermiteLagrange t i).eval (t j) = 0 := by
  exact Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)

@[simp]
theorem hermiteValueBasis_eval {t : Fin 5 → ℝ} (ht : Function.Injective t) (i j : Fin 5) :
    (hermiteValueBasis t i).eval (t j) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst j
    simp [hermiteValueBasis, hermiteLagrange_eval_self ht]
  · simp [hermiteValueBasis, hermiteLagrange_eval_of_ne hij]

@[simp]
theorem hermiteSlopeBasis_eval {t : Fin 5 → ℝ} (i j : Fin 5) :
    (hermiteSlopeBasis t i).eval (t j) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteSlopeBasis]
  · simp [hermiteSlopeBasis, hermiteLagrange_eval_of_ne hij]

@[simp]
theorem hermiteValueBasis_derivative_eval {t : Fin 5 → ℝ} (ht : Function.Injective t)
    (i j : Fin 5) : (hermiteValueBasis t i).derivative.eval (t j) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteValueBasis, derivative_pow, hermiteLagrange_eval_self ht]
  · simp [hermiteValueBasis, derivative_pow, hermiteLagrange_eval_of_ne hij]

@[simp]
theorem hermiteSlopeBasis_derivative_eval {t : Fin 5 → ℝ} (ht : Function.Injective t)
    (i j : Fin 5) :
    (hermiteSlopeBasis t i).derivative.eval (t j) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst j
    simp [hermiteSlopeBasis, derivative_pow, hermiteLagrange_eval_self ht]
  · simp [hermiteSlopeBasis, derivative_pow, hermiteLagrange_eval_of_ne hij]

@[simp]
theorem hermiteInterpolant_eval {t value slope : Fin 5 → ℝ} (ht : Function.Injective t)
    (i : Fin 5) : (hermiteInterpolant t value slope).eval (t i) = value i := by
  classical
  unfold hermiteInterpolant
  rw [eval_add]
  change (evalRingHom (t i)) (∑ j, C (value j) * hermiteValueBasis t j) +
    (evalRingHom (t i)) (∑ j, C (slope j) * hermiteSlopeBasis t j) = value i
  rw [map_sum, map_sum]
  simp only [coe_evalRingHom, eval_mul, eval_C]
  simp [hermiteValueBasis_eval ht, hermiteSlopeBasis_eval]

@[simp]
theorem hermiteInterpolant_derivative_eval {t value slope : Fin 5 → ℝ}
    (ht : Function.Injective t) (i : Fin 5) :
    (hermiteInterpolant t value slope).derivative.eval (t i) = slope i := by
  classical
  unfold hermiteInterpolant
  rw [map_add, map_sum, map_sum]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  rw [eval_add]
  change (evalRingHom (t i))
      (∑ j, C (value j) * (hermiteValueBasis t j).derivative) +
    (evalRingHom (t i))
      (∑ j, C (slope j) * (hermiteSlopeBasis t j).derivative) = slope i
  rw [map_sum, map_sum]
  simp only [coe_evalRingHom, eval_mul, eval_C]
  simp [hermiteValueBasis_derivative_eval ht, hermiteSlopeBasis_derivative_eval ht]

@[simp]
theorem hermiteNodal_eval_node (t : Fin 5 → ℝ) (i : Fin 5) :
    (hermiteNodal t).eval (t i) = 0 := by
  rw [hermiteNodal, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

@[simp]
theorem hermiteNodal_derivative_eval_node (t : Fin 5 → ℝ) (i : Fin 5) :
    (hermiteNodal t).derivative.eval (t i) = 0 := by
  classical
  rw [hermiteNodal, ← Finset.mul_prod_erase Finset.univ
    (fun j ↦ (X - C (t j)) ^ 2) (Finset.mem_univ i), derivative_mul, eval_add,
    eval_mul, eval_mul]
  simp [derivative_pow]

theorem hermiteNodal_eval_zero_ne {t : Fin 5 → ℝ} (ht0 : ∀ i, t i ≠ 0) :
    (hermiteNodal t).eval 0 ≠ 0 := by
  simp only [hermiteNodal, eval_prod, eval_pow, eval_sub, eval_X, eval_C, zero_sub]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero 2 (neg_ne_zero.mpr (ht0 i))

theorem hermiteLagrange_natDegree {t : Fin 5 → ℝ} (ht : Function.Injective t)
    (i : Fin 5) : (hermiteLagrange t i).natDegree = 4 := by
  rw [hermiteLagrange, Lagrange.natDegree_basis ht.injOn (Finset.mem_univ i)]
  norm_num

theorem hermiteValueBasis_natDegree_le {t : Fin 5 → ℝ} (ht : Function.Injective t)
    (i : Fin 5) : (hermiteValueBasis t i).natDegree ≤ 9 := by
  unfold hermiteValueBasis
  calc
    _ ≤ (1 - C (2 * (hermiteLagrange t i).derivative.eval (t i)) *
          (X - C (t i))).natDegree + ((hermiteLagrange t i) ^ 2).natDegree :=
      natDegree_mul_le
    _ ≤ 1 + 8 := by
      have hc : (C (2 * (hermiteLagrange t i).derivative.eval (t i)) *
          (X - C (t i))).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans (by simp)
      have hleft : (1 - C (2 * (hermiteLagrange t i).derivative.eval (t i)) *
          (X - C (t i))).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le (by simp) hc)
      have hright : ((hermiteLagrange t i) ^ 2).natDegree ≤ 8 :=
        natDegree_pow_le.trans (by rw [hermiteLagrange_natDegree ht])
      omega
    _ = 9 := rfl

theorem hermiteSlopeBasis_natDegree_le {t : Fin 5 → ℝ} (ht : Function.Injective t)
    (i : Fin 5) : (hermiteSlopeBasis t i).natDegree ≤ 9 := by
  unfold hermiteSlopeBasis
  calc
    _ ≤ (X - C (t i)).natDegree + ((hermiteLagrange t i) ^ 2).natDegree :=
      natDegree_mul_le
    _ ≤ 1 + 8 := by
      have hleft : (X - C (t i)).natDegree ≤ 1 := by simp
      have hright : ((hermiteLagrange t i) ^ 2).natDegree ≤ 8 :=
        natDegree_pow_le.trans (by rw [hermiteLagrange_natDegree ht])
      omega
    _ = 9 := rfl

theorem hermiteInterpolant_natDegree_le {t value slope : Fin 5 → ℝ}
    (ht : Function.Injective t) : (hermiteInterpolant t value slope).natDegree ≤ 9 := by
  unfold hermiteInterpolant
  apply natDegree_add_le_of_degree_le
  · apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans (hermiteValueBasis_natDegree_le ht i)
  · apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans (hermiteSlopeBasis_natDegree_le ht i)

theorem hermiteNodal_natDegree_le (t : Fin 5 → ℝ) : (hermiteNodal t).natDegree ≤ 10 := by
  unfold hermiteNodal
  calc
    _ ≤ ∑ i, ((X - C (t i)) ^ 2 : ℝ[X]).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _ : Fin 5, 2 := Finset.sum_le_sum fun i _ ↦
      natDegree_pow_le.trans (by simp)
    _ = 10 := by norm_num

theorem hermiteNodal_monic (t : Fin 5 → ℝ) : (hermiteNodal t).Monic := by
  rw [hermiteNodal]
  apply monic_prod_of_monic
  intro i _
  exact (monic_X_sub_C (t i)).pow 2

theorem hermiteNodal_natDegree (t : Fin 5 → ℝ) : (hermiteNodal t).natDegree = 10 := by
  rw [hermiteNodal, natDegree_prod]
  · simp
  · intro i _
    exact pow_ne_zero _ (X_sub_C_ne_zero (t i))

theorem hermiteZeroInterpolant_natDegree_le {t value slope : Fin 5 → ℝ}
    (ht : Function.Injective t) : (hermiteZeroInterpolant t value slope).natDegree ≤ 10 := by
  dsimp only [hermiteZeroInterpolant]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (hermiteInterpolant_natDegree_le ht).trans (by norm_num)
  · exact (natDegree_C_mul_le _ _).trans (hermiteNodal_natDegree_le t)

@[simp]
theorem hermiteZeroInterpolant_eval_zero {t value slope : Fin 5 → ℝ}
    (ht0 : ∀ i, t i ≠ 0) : (hermiteZeroInterpolant t value slope).eval 0 = 0 := by
  simp [hermiteZeroInterpolant, hermiteNodal_eval_zero_ne ht0]

@[simp]
theorem hermiteZeroInterpolant_eval {t value slope : Fin 5 → ℝ}
    (ht : Function.Injective t) (i : Fin 5) :
    (hermiteZeroInterpolant t value slope).eval (t i) = value i := by
  simp [hermiteZeroInterpolant, hermiteInterpolant_eval ht]

@[simp]
theorem hermiteZeroInterpolant_derivative_eval {t value slope : Fin 5 → ℝ}
    (ht : Function.Injective t) (i : Fin 5) :
    (hermiteZeroInterpolant t value slope).derivative.eval (t i) = slope i := by
  simp [hermiteZeroInterpolant, hermiteInterpolant_derivative_eval ht]

/-- The interpolation conditions from the paper, separated from the semantic
majorization theorem. -/
def IsHermiteInterpolant (α : ℝ) (t : Fin 5 → ℝ) (P : ℝ[X]) : Prop :=
  P.natDegree ≤ 10 ∧ P.coeff 0 = 0 ∧
    (∀ i, P.eval (t i) = (t i).rpow α) ∧
    ∀ i, P.derivative.eval (t i) = α * (t i).rpow (α - 1)

theorem isHermiteInterpolant_hermiteZeroInterpolant {α : ℝ} {t : Fin 5 → ℝ}
    (ht : Function.Injective t) (ht0 : ∀ i, t i ≠ 0) :
    IsHermiteInterpolant α t
      (hermiteZeroInterpolant t (fun i ↦ (t i).rpow α)
        (fun i ↦ α * (t i).rpow (α - 1))) := by
  refine ⟨hermiteZeroInterpolant_natDegree_le ht, ?_, ?_, ?_⟩
  · rw [coeff_zero_eq_eval_zero]
    exact hermiteZeroInterpolant_eval_zero ht0
  · exact hermiteZeroInterpolant_eval ht
  · exact hermiteZeroInterpolant_derivative_eval ht

private theorem isHermiteInterpolant_unique {α : ℝ} {t : Fin 5 → ℝ}
    (ht : StrictMono t) (ht0 : 0 < t 0) {P Q : ℝ[X]}
    (hP : IsHermiteInterpolant α t P) (hQ : IsHermiteInterpolant α t Q) : P = Q := by
  let R := P - Q
  have hRdegree : R.natDegree ≤ 10 := by
    exact (natDegree_sub_le _ _).trans (max_le hP.1 hQ.1)
  have hRzero : R.eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero]
    exact sub_eq_zero.mpr (hP.2.1.trans hQ.2.1.symm)
  have hRnode (i : Fin 5) : R.eval (t i) = 0 := by
    simp only [R, eval_sub]
    exact sub_eq_zero.mpr (hP.2.2.1 i |>.trans (hQ.2.2.1 i).symm)
  have hRderivNode (i : Fin 5) : R.derivative.eval (t i) = 0 := by
    simp only [R, derivative_sub, eval_sub]
    exact sub_eq_zero.mpr (hP.2.2.2 i |>.trans (hQ.2.2.2 i).symm)
  have ht01 : t 0 < t 1 := ht (by decide)
  have ht12 : t 1 < t 2 := ht (by decide)
  have ht23 : t 2 < t 3 := ht (by decide)
  have ht34 : t 3 < t 4 := ht (by decide)
  obtain ⟨r0, hr0, hr0zero⟩ :=
    exists_deriv_eq_zero ht0 R.continuousOn (hRzero.trans (hRnode 0).symm)
  obtain ⟨r1, hr1, hr1zero⟩ :=
    exists_deriv_eq_zero ht01 R.continuousOn ((hRnode 0).trans (hRnode 1).symm)
  obtain ⟨r2, hr2, hr2zero⟩ :=
    exists_deriv_eq_zero ht12 R.continuousOn ((hRnode 1).trans (hRnode 2).symm)
  obtain ⟨r3, hr3, hr3zero⟩ :=
    exists_deriv_eq_zero ht23 R.continuousOn ((hRnode 2).trans (hRnode 3).symm)
  obtain ⟨r4, hr4, hr4zero⟩ :=
    exists_deriv_eq_zero ht34 R.continuousOn ((hRnode 3).trans (hRnode 4).symm)
  rcases hr0 with ⟨hr0l, hr0r⟩
  rcases hr1 with ⟨hr1l, hr1r⟩
  rcases hr2 with ⟨hr2l, hr2r⟩
  rcases hr3 with ⟨hr3l, hr3r⟩
  rcases hr4 with ⟨hr4l, hr4r⟩
  rw [R.deriv] at hr0zero hr1zero hr2zero hr3zero hr4zero
  let roots : Fin 10 → ℝ := ![r0, t 0, r1, t 1, r2, t 2, r3, t 3, r4, t 4]
  have hrootsMono : StrictMono roots := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simp [roots] <;> omega
  have hrootsZero (i : Fin 10) : R.derivative.eval (roots i) = 0 := by
    fin_cases i <;> simp [roots, hr0zero, hr1zero, hr2zero, hr3zero, hr4zero,
      hRderivNode]
  have hRderivative : R.derivative = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero R.derivative hrootsMono.injective
      hrootsZero <| by
        have hdegree : R.derivative.natDegree ≤ 9 :=
          (natDegree_derivative_le R).trans (by omega)
        simpa using (show R.derivative.natDegree < 10 by omega)
  have hRcoeff : R.coeff 0 = 0 := by rwa [coeff_zero_eq_eval_zero]
  have hReq : R = 0 := by
    rw [eq_C_of_derivative_eq_zero hRderivative, hRcoeff, C_0]
  exact sub_eq_zero.mp hReq

/-- The ten interpolation equations and zero constant term determine a unique
degree-at-most-ten polynomial. -/
theorem existsUnique_isHermiteInterpolant {α : ℝ} {t : Fin 5 → ℝ}
    (ht : StrictMono t) (ht0 : 0 < t 0) : ∃! P, IsHermiteInterpolant α t P := by
  have htInjective : Function.Injective t := ht.injective
  have htNonzero : ∀ i, t i ≠ 0 := fun i ↦ ne_of_gt <| ht0.trans_le <| ht.monotone (Fin.zero_le i)
  refine ⟨hermiteZeroInterpolant t (fun i ↦ (t i).rpow α)
      (fun i ↦ α * (t i).rpow (α - 1)),
    isHermiteInterpolant_hermiteZeroInterpolant htInjective htNonzero, ?_⟩
  intro Q hQ
  exact isHermiteInterpolant_unique ht ht0 hQ
    (isHermiteInterpolant_hermiteZeroInterpolant htInjective htNonzero)

/-- The explicit, uniquely determined paper interpolant. -/
noncomputable def chosenHermiteInterpolant (α : ℝ) (t : Fin 5 → ℝ) : ℝ[X] :=
  hermiteZeroInterpolant t (fun i ↦ (t i).rpow α)
    (fun i ↦ α * (t i).rpow (α - 1))

/-- The same five-node Hermite polynomial, normalized to interpolate `u^α`
at an auxiliary point `δ`. -/
noncomputable def hermiteAuxiliaryInterpolant (α δ : ℝ) (t : Fin 5 → ℝ) : ℝ[X] :=
  let Q := hermiteInterpolant t (fun i ↦ (t i).rpow α)
    (fun i ↦ α * (t i).rpow (α - 1))
  Q + C ((δ.rpow α - Q.eval δ) / (hermiteNodal t).eval δ) * hermiteNodal t

theorem chosenHermiteInterpolant_isHermiteInterpolant (α : ℝ) (t : Fin 5 → ℝ)
    (ht : StrictMono t) (ht0 : 0 < t 0) :
    IsHermiteInterpolant α t (chosenHermiteInterpolant α t) :=
  isHermiteInterpolant_hermiteZeroInterpolant ht.injective fun i ↦
    ne_of_gt <| ht0.trans_le <| ht.monotone (Fin.zero_le i)

/-- The chosen interpolant is the explicit Hermite basis plus the nodal
correction that enforces its zero constant coefficient. -/
theorem chosenHermiteInterpolant_eq_hermiteZeroInterpolant (α : ℝ) (t : Fin 5 → ℝ) :
    chosenHermiteInterpolant α t =
      hermiteZeroInterpolant t (fun i ↦ (t i).rpow α)
        (fun i ↦ α * (t i).rpow (α - 1)) := rfl

/-- The explicit public interpolant is the unique polynomial characterized by
the paper's ten equations and zero constant coefficient. -/
theorem eq_chosenHermiteInterpolant_of_isHermiteInterpolant (α : ℝ) (t : Fin 5 → ℝ)
    (ht : StrictMono t) (ht0 : 0 < t 0) :
    ∀ P, IsHermiteInterpolant α t P → P = chosenHermiteInterpolant α t := by
  intro P hP
  exact isHermiteInterpolant_unique ht ht0 hP
    (chosenHermiteInterpolant_isHermiteInterpolant α t ht ht0)

theorem chosenHermiteInterpolant_natDegree_le (α : ℝ) (t : Fin 5 → ℝ)
    (ht : StrictMono t) (ht0 : 0 < t 0) :
    (chosenHermiteInterpolant α t).natDegree ≤ 10 :=
  (chosenHermiteInterpolant_isHermiteInterpolant α t ht ht0).1

@[simp]
theorem chosenHermiteInterpolant_coeff_zero (α : ℝ) (t : Fin 5 → ℝ)
    (ht : StrictMono t) (ht0 : 0 < t 0) :
    (chosenHermiteInterpolant α t).coeff 0 = 0 :=
  (chosenHermiteInterpolant_isHermiteInterpolant α t ht ht0).2.1

@[simp]
theorem chosenHermiteInterpolant_eval_node (α : ℝ) (t : Fin 5 → ℝ)
    (ht : StrictMono t) (ht0 : 0 < t 0) (i : Fin 5) :
    (chosenHermiteInterpolant α t).eval (t i) = (t i).rpow α :=
  (chosenHermiteInterpolant_isHermiteInterpolant α t ht ht0).2.2.1 i

@[simp]
theorem chosenHermiteInterpolant_derivative_eval_node (α : ℝ) (t : Fin 5 → ℝ)
    (ht : StrictMono t) (ht0 : 0 < t 0) (i : Fin 5) :
    (chosenHermiteInterpolant α t).derivative.eval (t i) =
      α * (t i).rpow (α - 1) :=
  (chosenHermiteInterpolant_isHermiteInterpolant α t ht ht0).2.2.2 i

@[simp]
theorem chosenHermiteInterpolant_eval_zero (α : ℝ) (t : Fin 5 → ℝ)
    (ht : StrictMono t) (ht0 : 0 < t 0) :
    (chosenHermiteInterpolant α t).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero]
  exact chosenHermiteInterpolant_coeff_zero α t ht ht0

private theorem exists_iterate_deriv_eq_zero_of_strictMono_zeros {n : ℕ}
    (f : ℝ → ℝ) (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hxpos : ∀ i, 0 < x i)
    (hcont : ∀ k ≤ n, ContinuousOn (deriv^[k] f) (Set.Ioi 0))
    (hzero : ∀ i, f (x i) = 0) : ∃ c, 0 < c ∧ (deriv^[n] f) c = 0 := by
  induction n generalizing f with
  | zero =>
      exact ⟨x 0, hxpos 0, hzero 0⟩
  | succ n ih =>
      have hrolle (i : Fin (n + 1)) :
          ∃ c ∈ Set.Ioo (x i.castSucc) (x i.succ), deriv f c = 0 := by
        apply exists_deriv_eq_zero (hx (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
        · apply (hcont 0 (Nat.zero_le _)).mono
          intro z hz
          exact lt_of_lt_of_le (hxpos i.castSucc) hz.1
        · rw [hzero, hzero]
      let y : Fin (n + 1) → ℝ := fun i ↦ Classical.choose (hrolle i)
      have hyMem (i : Fin (n + 1)) :
          y i ∈ Set.Ioo (x i.castSucc) (x i.succ) :=
        (Classical.choose_spec (hrolle i)).1
      have hyZero (i : Fin (n + 1)) : deriv f (y i) = 0 :=
        (Classical.choose_spec (hrolle i)).2
      have hyMono : StrictMono y := by
        rw [Fin.strictMono_iff_lt_succ]
        intro i
        calc
          y i.castSucc < x i.castSucc.succ := (hyMem i.castSucc).2
          _ = x i.succ.castSucc := by congr 1
          _ < y i.succ := (hyMem i.succ).1
      have hyPos (i : Fin (n + 1)) : 0 < y i :=
        (hxpos i.castSucc).trans (hyMem i).1
      obtain ⟨c, hcpos, hc⟩ := ih (deriv f) y hyMono hyPos (fun k hk ↦ by
        simpa only [Function.iterate_succ_apply] using hcont k.succ (Nat.succ_le_succ hk)) hyZero
      exact ⟨c, hcpos, by simpa only [Function.iterate_succ_apply] using hc⟩

/-- Elevenfold Rolle theorem tailored to the Hermite remainder: seven distinct
positive zeros, five of them double, force a positive zero of the eleventh
derivative. -/
theorem exists_pos_iter_deriv_eleven_eq_zero_of_seven_zeros_five_double
    (f : ℝ → ℝ) (s double : Finset ℝ) (hs : s.card = 7)
    (hdouble : double ⊆ s) (hdoubleCard : double.card = 5)
    (hpos : ∀ x ∈ s, 0 < x) (hzero : ∀ x ∈ s, f x = 0)
    (hdoubleZero : ∀ x ∈ double, deriv f x = 0)
    (hcont : ∀ k ≤ 11, ContinuousOn (deriv^[k] f) (Set.Ioi 0)) :
    ∃ c, 0 < c ∧ (deriv^[11] f) c = 0 := by
  let ordered : Fin 7 ↪o ℝ := s.orderEmbOfFin hs
  have hrolle (i : Fin 6) :
      ∃ c ∈ Set.Ioo (ordered i.castSucc) (ordered i.succ), deriv f c = 0 := by
    apply exists_deriv_eq_zero (ordered.strictMono Fin.castSucc_lt_succ)
    · apply (hcont 0 (by omega)).mono
      intro z hz
      exact lt_of_lt_of_le (hpos _ (s.orderEmbOfFin_mem hs i.castSucc)) hz.1
    · rw [hzero _ (s.orderEmbOfFin_mem hs _), hzero _ (s.orderEmbOfFin_mem hs _)]
  let between : Fin 6 → ℝ := fun i ↦ Classical.choose (hrolle i)
  have hbetweenMem (i : Fin 6) :
      between i ∈ Set.Ioo (ordered i.castSucc) (ordered i.succ) :=
    (Classical.choose_spec (hrolle i)).1
  have hbetweenZero (i : Fin 6) : deriv f (between i) = 0 :=
    (Classical.choose_spec (hrolle i)).2
  have hbetweenMono : StrictMono between := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    calc
      between i.castSucc < ordered i.castSucc.succ := (hbetweenMem i.castSucc).2
      _ = ordered i.succ.castSucc := by congr 1
      _ < between i.succ := (hbetweenMem i.succ).1
  have hbetweenNotMem (i : Fin 6) : between i ∉ s := by
    intro hi
    have hiRange : between i ∈ Set.range ordered := by
      rw [s.range_orderEmbOfFin hs]
      exact hi
    obtain ⟨j, hj⟩ := hiRange
    have hijLeft : i.castSucc < j := ordered.lt_iff_lt.mp <| by
      simpa [hj] using (hbetweenMem i).1
    have hijRight : j < i.succ := ordered.lt_iff_lt.mp <| by
      simpa [hj] using (hbetweenMem i).2
    have hAdjacent : i.succ.val = i.castSucc.val + 1 := rfl
    omega
  let betweenSet : Finset ℝ := Finset.univ.image between
  have hbetweenCard : betweenSet.card = 6 := by
    rw [Finset.card_image_of_injective _ hbetweenMono.injective, Finset.card_univ,
      Fintype.card_fin]
  have hdisjoint : Disjoint betweenSet double := by
    rw [Finset.disjoint_left]
    intro x hx hxd
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hbetweenNotMem i (hdouble hxd)
  let roots := betweenSet ∪ double
  have hrootsCard : roots.card = 11 := by
    dsimp only [roots]
    rw [Finset.card_union_of_disjoint hdisjoint, hbetweenCard, hdoubleCard]
  let rootOrder : Fin 11 ↪o ℝ := roots.orderEmbOfFin hrootsCard
  have hrootOrderPos (i : Fin 11) : 0 < rootOrder i := by
    have hi := roots.orderEmbOfFin_mem hrootsCard i
    dsimp only [roots] at hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · dsimp only [betweenSet] at hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, _, hj⟩ := hi
      rw [← hj]
      exact (hpos _ (s.orderEmbOfFin_mem hs j.castSucc)).trans (hbetweenMem j).1
    · exact hpos _ (hdouble hi)
  have hrootOrderZero (i : Fin 11) : deriv f (rootOrder i) = 0 := by
    have hi := roots.orderEmbOfFin_mem hrootsCard i
    dsimp only [roots] at hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · dsimp only [betweenSet] at hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, _, hj⟩ := hi
      rw [← hj]
      exact hbetweenZero j
    · exact hdoubleZero _ hi
  obtain ⟨c, hcpos, hc⟩ := exists_iterate_deriv_eq_zero_of_strictMono_zeros
    (deriv f) rootOrder rootOrder.strictMono hrootOrderPos (fun k hk ↦ by
      simpa only [Function.iterate_succ_apply] using hcont k.succ (by omega)) hrootOrderZero
  exact ⟨c, hcpos, by simpa only [Function.iterate_succ_apply] using hc⟩

/-- For `1 < α < 2`, the eleventh derivative of `u ↦ u^α` is strictly
negative at every positive point. -/
theorem iter_deriv_rpow_eleven_neg {α x : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2)
    (hx : 0 < x) : (deriv^[11] (fun u : ℝ ↦ u.rpow α)) x < 0 := by
  change (deriv^[11] (fun u : ℝ ↦ u ^ α)) x < 0
  rw [Real.iter_deriv_rpow_const]
  have hcoeff : (descPochhammer ℝ 11).eval α < 0 := by
    calc
      _ = -(α * (α - 1) * (2 - α) * (3 - α) * (4 - α) * (5 - α) *
          (6 - α) * (7 - α) * (8 - α) * (9 - α) * (10 - α)) := by
        rw [descPochhammer_eval_eq_prod_range]
        norm_num [Finset.prod_range_succ]
        ring
      _ < 0 := by
        rw [neg_lt_zero]
        have h3 : 0 < 3 - α := by linarith
        have h4 : 0 < 4 - α := by linarith
        have h5 : 0 < 5 - α := by linarith
        have h6 : 0 < 6 - α := by linarith
        have h7 : 0 < 7 - α := by linarith
        have h8 : 0 < 8 - α := by linarith
        have h9 : 0 < 9 - α := by linarith
        have h10 : 0 < 10 - α := by linarith
        positivity
  exact mul_neg_of_neg_of_pos hcoeff (Real.rpow_pos_of_pos hx _)

private theorem iterate_deriv_polynomial_eval (P : ℝ[X]) (n : ℕ) (x : ℝ) :
    (deriv^[n] (fun y : ℝ ↦ P.eval y)) x = (derivative^[n] P).eval x := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hderiv : deriv (fun y : ℝ ↦ P.eval y) = fun y ↦ P.derivative.eval y :=
        _root_.funext fun y ↦ (P.hasDerivAt y).deriv
      rw [hderiv]
      exact ih P.derivative

private theorem iterate_derivative_eleven_eval_pos_of_monic_natDegree
    {P : ℝ[X]} (hPmonic : P.Monic) (hPdegree : P.natDegree = 11) (x : ℝ) :
    0 < (derivative^[11] P).eval x := by
  have hdegree : (derivative^[11] P).natDegree = 0 := by
    exact le_antisymm ((natDegree_iterate_derivative P 11).trans_eq (by simp [hPdegree]))
      (Nat.zero_le _)
  rw [eq_C_of_natDegree_eq_zero hdegree, eval_C]
  rw [coeff_iterate_derivative]
  have hcoeff : P.coeff 11 = 1 := by
    rw [← hPdegree]
    exact hPmonic.coeff_natDegree
  norm_num [hcoeff]

private theorem contDiff_polynomial_eval (P : ℝ[X]) : ∀ n : ℕ,
    ContDiff ℝ n (fun y : ℝ ↦ P.eval y) := by
  intro n
  induction n generalizing P with
  | zero => exact contDiff_zero.2 P.continuous
  | succ n ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨P.differentiable, by simp, ?_⟩
      have hderiv : deriv (fun y : ℝ ↦ P.eval y) = fun y ↦ P.derivative.eval y :=
        _root_.funext fun y ↦ (P.hasDerivAt y).deriv
      rw [hderiv]
      exact ih P.derivative

private theorem hermiteError_continuousOn_iterate_deriv
    (α c : ℝ) (P W : ℝ[X]) :
    ∀ k ≤ 11, ContinuousOn
      (deriv^[k] (fun x : ℝ ↦ x.rpow α - P.eval x - c * W.eval x)) (Set.Ioi 0) := by
  have hg : ContDiffOn ℝ 11
      (fun x : ℝ ↦ x.rpow α - P.eval x - c * W.eval x) (Set.Ioi 0) := by
    intro x hx
    exact (((Real.contDiffAt_rpow_const_of_ne hx.ne').sub
      (contDiff_polynomial_eval P 11).contDiffAt).sub
        ((contDiff_const.mul (contDiff_polynomial_eval W 11)).contDiffAt)).contDiffWithinAt
  intro k hk
  have hc := hg.continuousOn_iteratedDerivWithin
    (show (k : WithTop ℕ∞) ≤ 11 by exact_mod_cast hk) isOpen_Ioi.uniqueDiffOn
  exact hc.congr (iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi).symm

private theorem hermiteError_iterate_deriv_eleven
    (α c x : ℝ) (P W : ℝ[X]) (hx : 0 < x) :
    (deriv^[11] (fun y : ℝ ↦ y.rpow α - P.eval y - c * W.eval y)) x =
      (deriv^[11] (fun y : ℝ ↦ y.rpow α)) x -
        (derivative^[11] P).eval x - c * (derivative^[11] W).eval x := by
  rw [← iteratedDeriv_eq_iterate]
  have hr : ContDiffAt ℝ 11 (fun y : ℝ ↦ y.rpow α) x :=
    Real.contDiffAt_rpow_const_of_ne hx.ne'
  have hP : ContDiffAt ℝ 11 (fun y : ℝ ↦ P.eval y) x :=
    (contDiff_polynomial_eval P 11).contDiffAt
  have hW : ContDiffAt ℝ 11 (fun y : ℝ ↦ c * W.eval y) x :=
    (contDiff_const.mul (contDiff_polynomial_eval W 11)).contDiffAt
  rw [iteratedDeriv_fun_sub (hr.sub hP) hW, iteratedDeriv_fun_sub hr hP,
    iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate]
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iterate_deriv_polynomial_eval, iterate_deriv_polynomial_eval]

/-- Hermite remainder inequality with a positive auxiliary interpolation
node.  This is the Rolle-theoretic core used before sending the auxiliary
node to zero. -/
theorem hermite_auxiliary_majorizes {α δ u : ℝ} {t : Fin 5 → ℝ} {P : ℝ[X]}
    (hα₁ : 1 < α) (hα₂ : α < 2) (ht : StrictMono t) (hδ : 0 < δ)
    (hδt : δ < t 0) (hδu : δ < u) (hu : ∀ i, u ≠ t i)
    (hPdegree : P.natDegree ≤ 10) (hPδ : P.eval δ = δ.rpow α)
    (hPvalue : ∀ i, P.eval (t i) = (t i).rpow α)
    (hPslope : ∀ i, P.derivative.eval (t i) = α * (t i).rpow (α - 1)) :
    u.rpow α ≤ P.eval u := by
  let W : ℝ[X] := (X - C δ) * hermiteNodal t
  have hWmonic : W.Monic := (monic_X_sub_C δ).mul (hermiteNodal_monic t)
  have hWdegree : W.natDegree = 11 := by
    dsimp only [W]
    rw [natDegree_mul (X_sub_C_ne_zero δ) (hermiteNodal_monic t).ne_zero,
      natDegree_X_sub_C, hermiteNodal_natDegree]
  have hWu : 0 < W.eval u := by
    dsimp only [W]
    rw [eval_mul, eval_sub, eval_X, eval_C]
    apply mul_pos (sub_pos.mpr hδu)
    rw [hermiteNodal, eval_prod]
    apply Finset.prod_pos
    intro i _
    rw [eval_pow, eval_sub, eval_X, eval_C]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr (hu i))
  by_contra hmajor
  have herror : 0 < u.rpow α - P.eval u := sub_pos.mpr (lt_of_not_ge hmajor)
  let c : ℝ := (u.rpow α - P.eval u) / W.eval u
  have hc : 0 < c := div_pos herror hWu
  let double : Finset ℝ := Finset.univ.image t
  have hdoubleCard : double.card = 5 := by
    dsimp only [double]
    rw [Finset.card_image_of_injective _ ht.injective, Finset.card_univ, Fintype.card_fin]
  have hδlt (i : Fin 5) : δ < t i := hδt.trans_le (ht.monotone (Fin.zero_le i))
  have hδnot : δ ∉ double := by
    rw [Finset.mem_image]
    rintro ⟨i, _, hi⟩
    exact (hδlt i).ne hi.symm
  have hunot : u ∉ double := by
    rw [Finset.mem_image]
    rintro ⟨i, _, hi⟩
    exact hu i hi.symm
  let s : Finset ℝ := insert δ (insert u double)
  have hδnot' : δ ∉ insert u double := by
    simp [hδnot, hδu.ne]
  have hs : s.card = 7 := by
    dsimp only [s]
    rw [Finset.card_insert_of_notMem hδnot', Finset.card_insert_of_notMem hunot,
      hdoubleCard]
  have hdouble : double ⊆ s := by
    intro x hx
    simp [s, hx]
  let g : ℝ → ℝ :=
    ((fun x : ℝ ↦ x.rpow α) - fun x ↦ P.eval x) -
      (fun _ ↦ c) * fun x ↦ W.eval x
  have hWδ : W.eval δ = 0 := by simp [W]
  have hWnode (i : Fin 5) : W.eval (t i) = 0 := by
    simp [W, hermiteNodal_eval_node]
  have hWnode' (i : Fin 5) : W.derivative.eval (t i) = 0 := by
    rw [derivative_mul, eval_add, eval_mul, eval_mul]
    simp [hermiteNodal_eval_node, hermiteNodal_derivative_eval_node]
  have hzero : ∀ x ∈ s, g x = 0 := by
    intro x hx
    simp only [s, double, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨i, _, rfl⟩
    · simp [g, hPδ, hWδ]
    · dsimp only [g, c]
      change x.rpow α - P.eval x -
        ((x.rpow α - P.eval x) / W.eval x) * W.eval x = 0
      rw [div_mul_cancel₀ _ hWu.ne']
      ring
    · simp [g, hPvalue, hWnode]
  have hdoubleZero : ∀ x ∈ double, deriv g x = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    have hr : HasDerivAt (fun x : ℝ ↦ x.rpow α)
        (α * (t i).rpow (α - 1)) (t i) := by
      simpa only [Real.rpow_eq_pow] using
        Real.hasDerivAt_rpow_const (x := t i) (p := α)
          (Or.inl (ne_of_gt (hδ.trans (hδlt i))))
    have hg' := (hr.sub (P.hasDerivAt (t i))).sub
      ((hasDerivAt_const (x := t i) c).mul (W.hasDerivAt (t i)))
    dsimp only [g]
    rw [hg'.deriv]
    simp [hPslope, hWnode, hWnode']
  have hpos : ∀ x ∈ s, 0 < x := by
    intro x hx
    simp only [s, double, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨i, _, rfl⟩
    · exact hδ
    · exact hδ.trans hδu
    · exact hδ.trans (hδlt i)
  obtain ⟨x, hx, hxzero⟩ :=
    exists_pos_iter_deriv_eleven_eq_zero_of_seven_zeros_five_double
      g s double hs hdouble hdoubleCard hpos hzero hdoubleZero
        (hermiteError_continuousOn_iterate_deriv α c P W)
  have hPeleven : derivative^[11] P = 0 :=
    iterate_derivative_eq_zero (lt_of_le_of_lt hPdegree (by omega))
  have hWpos : 0 < (derivative^[11] W).eval x :=
    iterate_derivative_eleven_eval_pos_of_monic_natDegree hWmonic hWdegree x
  have hrpowNeg := iter_deriv_rpow_eleven_neg hα₁ hα₂ hx
  have hgNeg : (deriv^[11] g) x < 0 := by
    rw [show g = (fun y : ℝ ↦ y.rpow α - P.eval y - c * W.eval y) from rfl,
      hermiteError_iterate_deriv_eleven α c x P W hx, hPeleven]
    simp only [eval_zero, sub_zero]
    exact sub_neg_of_lt (lt_of_lt_of_le hrpowNeg (mul_nonneg hc.le hWpos.le))
  exact hgNeg.ne hxzero

theorem hermiteNodal_eval_ne {x : ℝ} {t : Fin 5 → ℝ}
    (hx : ∀ i, x ≠ t i) : (hermiteNodal t).eval x ≠ 0 := by
  rw [hermiteNodal, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (hx i))

theorem hermiteAuxiliaryInterpolant_natDegree_le (α δ : ℝ) (t : Fin 5 → ℝ)
    (ht : Function.Injective t) :
    (hermiteAuxiliaryInterpolant α δ t).natDegree ≤ 10 := by
  let Q := hermiteInterpolant t (fun i ↦ (t i).rpow α)
    (fun i ↦ α * (t i).rpow (α - 1))
  dsimp only [hermiteAuxiliaryInterpolant]
  exact (natDegree_add_le _ _).trans <| max_le
    ((hermiteInterpolant_natDegree_le ht).trans (by omega)) <|
      (natDegree_C_mul_le _ _).trans (hermiteNodal_natDegree_le t)

@[simp]
theorem hermiteAuxiliaryInterpolant_eval_auxiliary (α δ : ℝ) (t : Fin 5 → ℝ)
    (hδ : ∀ i, δ ≠ t i) :
    (hermiteAuxiliaryInterpolant α δ t).eval δ = δ.rpow α := by
  rw [hermiteAuxiliaryInterpolant, eval_add, eval_mul, eval_C]
  rw [div_mul_cancel₀ _ (hermiteNodal_eval_ne hδ)]
  ring

@[simp]
theorem hermiteAuxiliaryInterpolant_eval_node (α δ : ℝ) (t : Fin 5 → ℝ)
    (ht : Function.Injective t) (i : Fin 5) :
    (hermiteAuxiliaryInterpolant α δ t).eval (t i) = (t i).rpow α := by
  simp [hermiteAuxiliaryInterpolant, hermiteInterpolant_eval ht,
    hermiteNodal_eval_node]

@[simp]
theorem hermiteAuxiliaryInterpolant_derivative_eval_node
    (α δ : ℝ) (t : Fin 5 → ℝ) (ht : Function.Injective t) (i : Fin 5) :
    (hermiteAuxiliaryInterpolant α δ t).derivative.eval (t i) =
      α * (t i).rpow (α - 1) := by
  simp [hermiteAuxiliaryInterpolant, derivative_add, derivative_mul,
    hermiteInterpolant_derivative_eval ht,
    hermiteNodal_derivative_eval_node]

theorem hermiteAuxiliaryInterpolant_majorizes {α δ u : ℝ} {t : Fin 5 → ℝ}
    (hα₁ : 1 < α) (hα₂ : α < 2) (ht : StrictMono t) (hδ : 0 < δ)
    (hδt : δ < t 0) (hδu : δ < u) (hu : ∀ i, u ≠ t i) :
    u.rpow α ≤ (hermiteAuxiliaryInterpolant α δ t).eval u := by
  apply hermite_auxiliary_majorizes hα₁ hα₂ ht hδ hδt hδu hu
    (hermiteAuxiliaryInterpolant_natDegree_le α δ t ht.injective)
  · exact hermiteAuxiliaryInterpolant_eval_auxiliary α δ t fun i ↦
      (hδt.trans_le (ht.monotone (Fin.zero_le i))).ne
  · exact hermiteAuxiliaryInterpolant_eval_node α δ t ht.injective
  · exact hermiteAuxiliaryInterpolant_derivative_eval_node α δ t ht.injective

theorem tendsto_hermiteAuxiliaryInterpolant_eval_zero {α u : ℝ} {t : Fin 5 → ℝ}
    (hα : 0 < α) (ht0 : 0 < t 0) (ht : StrictMono t) :
    Filter.Tendsto (fun δ ↦ (hermiteAuxiliaryInterpolant α δ t).eval u) (nhds 0)
      (nhds ((chosenHermiteInterpolant α t).eval u)) := by
  let Q := hermiteInterpolant t (fun i ↦ (t i).rpow α)
    (fun i ↦ α * (t i).rpow (α - 1))
  have hnodes : ∀ i, (0 : ℝ) ≠ t i := fun i ↦
    ne_of_lt (ht0.trans_le (ht.monotone (Fin.zero_le i)))
  have hN0 : (hermiteNodal t).eval 0 ≠ 0 := hermiteNodal_eval_ne hnodes
  have hrpow : ContinuousAt (fun δ : ℝ ↦ δ.rpow α) 0 := by
    simpa only [Real.rpow_eq_pow] using
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
  have hcontinuous : ContinuousAt
      (fun δ : ℝ ↦ Q.eval u +
        ((δ.rpow α - Q.eval δ) / (hermiteNodal t).eval δ) *
          (hermiteNodal t).eval u) 0 :=
    continuousAt_const.add <| ((hrpow.sub Q.continuous.continuousAt).div
      (hermiteNodal t).continuous.continuousAt hN0).mul continuousAt_const
  convert hcontinuous.tendsto using 1
  · ext δ
    simp [hermiteAuxiliaryInterpolant, Q]
  · simp [chosenHermiteInterpolant, hermiteZeroInterpolant, Q,
      Real.zero_rpow hα.ne']
    ring

/-- The degree-ten Hermite interpolant majorizes `u^α` on the nonnegative
half-line. -/
theorem chosenHermiteInterpolant_majorizes_of_nonneg {α : ℝ} {t : Fin 5 → ℝ}
    (hα₁ : 1 < α) (hα₂ : α < 2) (ht : StrictMono t)
    (ht0 : 0 < t 0) {u : ℝ} (hu0 : 0 ≤ u) :
    u.rpow α ≤ (chosenHermiteInterpolant α t).eval u := by
  rcases hu0.eq_or_lt with rfl | huPos
  · rw [chosenHermiteInterpolant_eval_zero α t ht ht0, Real.rpow_eq_pow,
      Real.zero_rpow]
    linarith
  by_cases hnode : ∃ i, u = t i
  · obtain ⟨i, rfl⟩ := hnode
    exact (chosenHermiteInterpolant_eval_node α t ht ht0 i).symm.le
  have huNode : ∀ i, u ≠ t i := by
    intro i hui
    exact hnode ⟨i, hui⟩
  have hlim := tendsto_hermiteAuxiliaryInterpolant_eval_zero
    (u := u) (t := t) (show 0 < α by linarith) ht0 ht
  have hlim' : Filter.Tendsto
      (fun δ ↦ (hermiteAuxiliaryInterpolant α δ t).eval u)
        (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((chosenHermiteInterpolant α t).eval u)) := hlim.mono_left inf_le_left
  apply ge_of_tendsto hlim'
  filter_upwards [Ioo_mem_nhdsGT ht0, Ioo_mem_nhdsGT huPos]
    with δ hδt hδu
  exact hermiteAuxiliaryInterpolant_majorizes hα₁ hα₂ ht hδt.1 hδt.2 hδu.2 huNode

/-- The paper's degree-ten Hermite interpolant majorizes `u^α` on the
entire closed unit interval.  The endpoints are included: zero follows from
the explicit normalization, while one is covered by the positive-point
auxiliary-node limit. -/
theorem chosenHermiteInterpolant_majorizes {α : ℝ} {t : Fin 5 → ℝ}
    (hα₁ : 1 < α) (hα₂ : α < 2) (ht : StrictMono t)
    (ht0 : 0 < t 0) (_ht1 : t 4 < 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    u.rpow α ≤ (chosenHermiteInterpolant α t).eval u :=
  chosenHermiteInterpolant_majorizes_of_nonneg hα₁ hα₂ ht ht0 hu.1

end CertifiedJL
