/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Fourier

/-!
# Half-amplitude compact residual support

For the large-modulus dominant branch we retain the dominant coordinate and
a residual subprofile with normalized residual mass in `[1/2,6/5)`.  A single
residual coefficient larger than `13/16` of the dominant amplitude is retained
directly.  Otherwise the usual greedy subset-sum lemma is run with target
`⌈A²/2⌉` and the sharper coordinate cap `⌊13A/16⌋²`.
-/

namespace CertifiedJL

/-- Integral ceiling of half a squared dominant amplitude. -/
def dominantHalfCutoffMass (amplitude : ℕ) : ℕ :=
  amplitude ^ 2 ⌈/⌉ 2

/-- Squared integral `13/16` coordinate cap. -/
def dominantThirteenSixteenthsCap (amplitude : ℕ) : ℕ :=
  ((13 * amplitude) / 16) ^ 2

private theorem halfCutoff_add_cap_lt_six_fifths
    (A : ℕ) (hA : 0 < A) :
    5 * (dominantHalfCutoffMass A + dominantThirteenSixteenthsCap A) <
      6 * A ^ 2 := by
  by_cases hsmall : A < 4
  · have ht : A ^ 2 ⌈/⌉ 2 ≤ (A ^ 2 + 1) / 2 := by
      apply (ceilDiv_le_iff_le_mul (by norm_num : (0 : ℕ) < 2)).2
      omega
    dsimp [dominantHalfCutoffMass, dominantThirteenSixteenthsCap]
    interval_cases A <;> omega
  have hAlarge : 4 ≤ A := le_of_not_gt hsmall
  let target := A ^ 2 ⌈/⌉ 2
  let rootCap := (13 * A) / 16
  have hceil : 2 * target ≤ A ^ 2 + 1 := by
    have ht : target ≤ (A ^ 2 + 1) / 2 := by
      dsimp [target]
      apply (ceilDiv_le_iff_le_mul (by norm_num : (0 : ℕ) < 2)).2
      omega
    omega
  have hfloor : 16 * rootCap ≤ 13 * A := by
    dsimp [rootCap]
    omega
  have hceilR : (2 : ℝ) * target ≤ A ^ 2 + 1 := by exact_mod_cast hceil
  have hfloorR : (16 : ℝ) * rootCap ≤ 13 * A := by exact_mod_cast hfloor
  have hroot : (0 : ℝ) ≤ rootCap := by positivity
  have hcapR : (256 : ℝ) * rootCap ^ 2 ≤ 169 * A ^ 2 := by nlinarith
  have hA2 : (16 : ℝ) ≤ A ^ 2 := by
    exact_mod_cast (Nat.pow_le_pow_left hAlarge 2)
  have hresultR : (5 : ℝ) * (target + rootCap ^ 2) < 6 * A ^ 2 := by
    nlinarith
  dsimp [dominantHalfCutoffMass, dominantThirteenSixteenthsCap,
    target, rootCap]
  exact_mod_cast hresultR

/-- If the residual mass is at least half the dominant square, a globally
maximal dominant coordinate admits a retained residual subprofile with mass
in `[A²/2,6A²/5)`.  The bounds are stated integrally, so there is no rounding
gap at small amplitudes. -/
theorem exists_halfCutoff_dominantRemainder_subprofile_with_dichotomy
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hi : w i ≠ 0)
    (hhigh : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) :
    ∃ support : Finset
        (Fin (Fintype.card (DominantRemainderIndex i))),
      dominantAmplitude w i ^ 2 ≤
        2 * sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) ∧
      5 * sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) <
        6 * dominantAmplitude w i ^ 2 ∧
      ((∃ j, j ∈ support ∧
          13 * dominantAmplitude w i <
            16 * (dominantRemainderFinWeights w i j).natAbs ∧
          (dominantRemainderFinWeights w i j).natAbs ^ 2 ≤
            dominantAmplitude w i ^ 2) ∨
        ∀ j, 16 * (dominantRemainderFinWeights w i j).natAbs ≤
          13 * dominantAmplitude w i) := by
  let n := Fintype.card (DominantRemainderIndex i)
  let v : Fin n → ℤ := dominantRemainderFinWeights w i
  let A := dominantAmplitude w i
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hbound : ∀ j, (v j).natAbs ^ 2 ≤ A ^ 2 := by
    intro j
    exact dominantRemainderFinWeights_sq_le_amplitude_sq_of_maximal
      w i hmax j
  by_cases hlarge : ∃ j, 13 * A < 16 * (v j).natAbs
  · obtain ⟨j, hj⟩ := hlarge
    have hsingleton :
        sqNorm (fun x => if x ∈ ({j} : Finset (Fin n)) then v x else 0) =
          (v j).natAbs ^ 2 := by
      unfold sqNorm
      calc
        ∑ x, (if x ∈ ({j} : Finset (Fin n)) then v x else 0).natAbs ^ 2 =
            ∑ x, if x = j then (v x).natAbs ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = j <;> simp [hx]
        _ = (v j).natAbs ^ 2 := by rw [Fintype.sum_ite_eq']
    refine ⟨{j}, ?_, ?_, Or.inl ⟨j, by simp, hj, hbound j⟩⟩
    · change A ^ 2 ≤
        2 * sqNorm (fun x => if x ∈ ({j} : Finset (Fin n)) then v x else 0)
      have hjR : (13 : ℝ) * A < 16 * (v j).natAbs := by exact_mod_cast hj
      have habs : (0 : ℝ) ≤ (v j).natAbs := by positivity
      have hlowerR : (A : ℝ) ^ 2 ≤ 2 * ((v j).natAbs : ℝ) ^ 2 := by
        nlinarith
      have hlower : A ^ 2 ≤ 2 * (v j).natAbs ^ 2 := by
        exact_mod_cast hlowerR
      rw [hsingleton]
      exact hlower
    · change 5 *
          sqNorm (fun x => if x ∈ ({j} : Finset (Fin n)) then v x else 0) <
        6 * A ^ 2
      have hjupper := hbound j
      change (v j).natAbs ^ 2 ≤ A ^ 2 at hjupper
      have hA2 : 0 < A ^ 2 := pow_pos hA _
      have hstrict : 5 * (v j).natAbs ^ 2 < 6 * A ^ 2 := by omega
      rw [hsingleton]
      exact hstrict
  · let target := dominantHalfCutoffMass A
    let cap := dominantThirteenSixteenthsCap A
    have hcoord : ∀ j, 16 * (v j).natAbs ≤ 13 * A := by
      intro j
      by_contra hcontra
      apply hlarge
      exact ⟨j, by omega⟩
    have hcap : ∀ j, (v j).natAbs ^ 2 ≤ cap := by
      intro j
      have hj := hcoord j
      have habs : (v j).natAbs ≤ (13 * A) / 16 := by omega
      exact Nat.pow_le_pow_left habs 2
    have hmassReal : (A : ℝ) ^ 2 ≤
        2 * (dominantRemainderSqNorm w i : ℝ) := by
      dsimp [dominantResidualRatio] at hhigh
      have hA2 : (0 : ℝ) < (A : ℝ) ^ 2 := sq_pos_of_pos hAreal
      have hmul := (le_div_iff₀ hA2).mp hhigh
      norm_num at hmul ⊢
      nlinarith
    have hmass : A ^ 2 ≤ 2 * dominantRemainderSqNorm w i := by
      dsimp [A] at hmassReal ⊢
      exact_mod_cast hmassReal
    have htargetPositive : 0 < target := by
      dsimp [target, dominantHalfCutoffMass]
      have hceil := le_smul_ceilDiv (by norm_num : (0 : ℕ) < 2)
        (b := A ^ 2)
      rw [Nat.nsmul_eq_mul] at hceil
      have hA2 : 0 < A ^ 2 := pow_pos hA _
      omega
    have htargetTotal : target ≤ dominantRemainderSqNorm w i := by
      dsimp [target, dominantHalfCutoffMass]
      exact (ceilDiv_le_iff_le_mul (by norm_num : (0 : ℕ) < 2)).2 hmass
    have htotal : target ≤ ∑ j, (v j).natAbs ^ 2 := by
      change target ≤ sqNorm v
      dsimp [v, n]
      rw [sqNorm_dominantRemainderFinWeights]
      exact htargetTotal
    obtain ⟨support, hlower, hupper⟩ :=
      exists_subset_sum_ge_lt_add_cap n target cap
        (fun j => (v j).natAbs ^ 2) htargetPositive hcap htotal
    have hsquare :
        sqNorm (fun j => if j ∈ support then v j else 0) =
          ∑ j ∈ support, (v j).natAbs ^ 2 := by
      unfold sqNorm
      calc
        ∑ j, (if j ∈ support then v j else 0).natAbs ^ 2 =
            ∑ j, if j ∈ support then (v j).natAbs ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j ∈ support <;> simp [hj]
        _ = ∑ j ∈ support, (v j).natAbs ^ 2 := by
          rw [← Finset.sum_filter]
          simp
    refine ⟨support, ?_, ?_, Or.inr hcoord⟩
    · rw [hsquare]
      have htargetLower : A ^ 2 ≤ 2 * target := by
        dsimp [target, dominantHalfCutoffMass]
        have hceil := le_smul_ceilDiv (by norm_num : (0 : ℕ) < 2)
          (b := A ^ 2)
        simpa [Nat.nsmul_eq_mul] using hceil
      exact htargetLower.trans (Nat.mul_le_mul_left 2 hlower)
    · rw [hsquare]
      change 5 * ∑ j ∈ support, (v j).natAbs ^ 2 < 6 * A ^ 2
      have hratio : 5 * (target + cap) < 6 * A ^ 2 := by
        dsimp [target, cap]
        exact halfCutoff_add_cap_lt_six_fifths A hA
      omega

/-- Compatibility projection of the exposed retained-support dichotomy. -/
theorem exists_halfCutoff_dominantRemainder_subprofile
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hi : w i ≠ 0)
    (hhigh : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) :
    ∃ support : Finset
        (Fin (Fintype.card (DominantRemainderIndex i))),
      dominantAmplitude w i ^ 2 ≤
        2 * sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) ∧
      5 * sqNorm (fun j => if j ∈ support then
          dominantRemainderFinWeights w i j else 0) <
        6 * dominantAmplitude w i ^ 2 := by
  obtain ⟨support, hlower, hupper, -⟩ :=
    exists_halfCutoff_dominantRemainder_subprofile_with_dichotomy
      w i hi hhigh hmax
  exact ⟨support, hlower, hupper⟩

/-- A cap on the canonical residual enumeration is the same cap on every
original coordinate other than the dominant one. -/
theorem dominantRemainder_coordinate_cap_of_fin_cap
    {d : ℕ} (w : Fin d → ℤ) (i j : Fin d)
    (hji : j ≠ i)
    (hcap : ∀ k, 16 * (dominantRemainderFinWeights w i k).natAbs ≤
      13 * dominantAmplitude w i) :
    16 * (w j).natAbs ≤ 13 * dominantAmplitude w i := by
  let k := dominantRemainderEquivFin i ⟨j, hji⟩
  have hk := hcap k
  simpa [k, dominantRemainderFinWeights] using hk

/-- Embed the canonical residual enumeration back into the original
coordinate space. -/
noncomputable def dominantRemainderEmbedding {d : ℕ} (i : Fin d) :
    Fin (Fintype.card (DominantRemainderIndex i)) ↪ Fin d :=
  ⟨fun j => ((dominantRemainderEquivFin i).symm j).1,
    fun a b h => by
      have hs : (dominantRemainderEquivFin i).symm a =
          (dominantRemainderEquivFin i).symm b := Subtype.ext h
      exact (dominantRemainderEquivFin i).symm.injective hs⟩

/-- Lift a residual support and include the dominant coordinate. -/
noncomputable def dominantLiftSupport {d : ℕ} (i : Fin d)
    (support : Finset (Fin (Fintype.card (DominantRemainderIndex i)))) :
    Finset (Fin d) :=
  insert i (support.map (dominantRemainderEmbedding i))

@[simp] theorem mem_dominantLiftSupport_i {d : ℕ} (i : Fin d)
    (support : Finset (Fin (Fintype.card (DominantRemainderIndex i)))) :
    i ∈ dominantLiftSupport i support := by
  simp [dominantLiftSupport]

/-- Restricting to the lifted support induces exactly the original canonical
residual restriction. -/
theorem dominantRemainderFinWeights_restrict_liftSupport
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (support : Finset (Fin (Fintype.card (DominantRemainderIndex i)))) :
    dominantRemainderFinWeights
        (fun j => if j ∈ dominantLiftSupport i support then w j else 0) i =
      fun j => if j ∈ support then dominantRemainderFinWeights w i j else 0 := by
  funext j
  unfold dominantRemainderFinWeights dominantLiftSupport
  simp only [Finset.mem_insert, Finset.mem_map]
  have hmem :
      (((dominantRemainderEquivFin i).symm j).1 = i ∨
          ∃ k ∈ support,
            dominantRemainderEmbedding i k =
              ((dominantRemainderEquivFin i).symm j).1) ↔
        j ∈ support := by
    constructor
    · intro h
      rcases h with hi | hs
      · exact ((dominantRemainderEquivFin i).symm j).2 hi |>.elim
      · rcases hs with ⟨k, hk, heq⟩
        have hkj : k = j := by
          apply (dominantRemainderEquivFin i).symm.injective
          exact Subtype.ext heq
        simpa [hkj] using hk
    · intro hj
      exact Or.inr ⟨j, hj, rfl⟩
  by_cases hs : j ∈ support
  · rw [if_pos hs, if_pos (hmem.mpr hs)]
  · rw [if_neg hs, if_neg (fun h => hs (hmem.mp h))]

end CertifiedJL
