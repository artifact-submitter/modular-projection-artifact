/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoAdjacent
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoTelescope

/-! # Concrete coordinate splits for the sparse upper Peano telescope -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CertifiedJL

/-- The weighted sum of all unchanged coordinates at one adjacent Peano
replacement. -/
noncomputable def upperPeanoAdjacentRestSumLaw {m : ℕ}
    (b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : Measure ℝ :=
  Measure.map (fun x : Fin m → ℝ => ∑ j, b (i.succAbove j) * x j)
    (Measure.pi (upperPeanoHybridRestCoordinateLaw i))

private theorem upperPeanoHybridValue_split_coordinate
    {m : ℕ} (b : Fin (m + 1) → ℝ) (s : ℂ) (i : Fin (m + 1))
    (k : ℕ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hmap : Measure.map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)
        (Measure.pi (upperPeanoHybridCoordinateLaw k)) =
      ν.prod (Measure.pi (upperPeanoHybridRestCoordinateLaw i)))
    (hint : Integrable (fun x : Fin (m + 1) → ℝ =>
      complexQuadraticExp s (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw k))) :
    upperPeanoHybridValue b s k =
        ∫ w, ∫ y : ℝ, complexQuadraticExp s (w + b i * y)
          ∂ν ∂upperPeanoAdjacentRestSumLaw b i ∧
      Integrable (fun w => ∫ y : ℝ,
        complexQuadraticExp s (w + b i * y) ∂ν)
        (upperPeanoAdjacentRestSumLaw b i) := by
  let (j : Fin (m + 1)) : IsProbabilityMeasure
      (upperPeanoHybridCoordinateLaw k j) := by
    unfold upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  let (j : Fin m) : IsProbabilityMeasure
      (upperPeanoHybridRestCoordinateLaw i j) := by
    unfold upperPeanoHybridRestCoordinateLaw upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  let F : (Fin (m + 1) → ℝ) → ℂ :=
    fun x => complexQuadraticExp s (∑ j, b j * x j)
  let g : ℝ × (Fin m → ℝ) → ℂ := fun p => F (e.symm p)
  let restSum : (Fin m → ℝ) → ℝ :=
    fun x => ∑ j, b (i.succAbove j) * x j
  let J : ℝ → ℂ := fun w =>
    ∫ y : ℝ, complexQuadraticExp s (w + b i * y) ∂ν
  have hFcont : Continuous F := by
    dsimp [F]
    apply (contDiff_complexQuadraticExp s).continuous.comp
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_apply j)
  have hgmeas : AEStronglyMeasurable g
      (Measure.map e (Measure.pi (upperPeanoHybridCoordinateLaw k))) :=
    (hFcont.measurable.comp e.symm.measurable).aestronglyMeasurable
  have hgmap : Integrable g
      (Measure.map e (Measure.pi (upperPeanoHybridCoordinateLaw k))) := by
    apply (integrable_map_measure (g := g) (f := e)
      hgmeas e.measurable.aemeasurable).mpr
    convert hint using 1
    funext x
    exact congrArg F (e.symm_apply_apply x)
  rw [hmap] at hgmap
  have hJcomp : Integrable (J ∘ restSum)
      (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
    refine hgmap.integral_prod_right.congr (ae_of_all _ fun x => ?_)
    apply integral_congr_ae
    filter_upwards [] with y
    rw [show g (y, x) =
        complexQuadraticExp s (restSum x + b i * y) by
      simp only [g, F, e, restSum]
      rw [weightedSum_piFinSuccAbove_symm b i]
      congr 1
      ring]
  have hJmeas : AEStronglyMeasurable J
      (upperPeanoAdjacentRestSumLaw b i) := by
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => complexQuadraticExp s (p.1 + b i * p.2))
        ((upperPeanoAdjacentRestSumLaw b i).prod ν) := by
      exact ((contDiff_complexQuadraticExp s).continuous.comp
        (continuous_fst.add
          (continuous_const.mul continuous_snd))).aestronglyMeasurable
    simpa [J] using hjoint.integral_prod_right'
  have hJ : Integrable J (upperPeanoAdjacentRestSumLaw b i) := by
    unfold upperPeanoAdjacentRestSumLaw
    have hrest : AEMeasurable restSum
        (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
      apply Continuous.aemeasurable
      dsimp [restSum]
      apply continuous_finsetSum
      intro j hj
      exact continuous_const.mul (continuous_apply j)
    exact (integrable_map_measure (g := J) (f := restSum)
      hJmeas hrest).mpr hJcomp
  refine ⟨?_, hJ⟩
  unfold upperPeanoHybridValue
  calc
    (∫ x, F x ∂Measure.pi (upperPeanoHybridCoordinateLaw k)) =
        ∫ p, g p ∂Measure.map e
          (Measure.pi (upperPeanoHybridCoordinateLaw k)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg F (e.symm_apply_apply x).symm
    _ = ∫ p, g p ∂ν.prod
          (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by rw [hmap]
    _ = ∫ x, J (restSum x)
          ∂Measure.pi (upperPeanoHybridRestCoordinateLaw i) := by
      rw [integral_prod_symm _ hgmap]
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show g (y, x) =
          complexQuadraticExp s (restSum x + b i * y) by
        simp only [g, F, e, restSum]
        rw [weightedSum_piFinSuccAbove_symm b i]
        congr 1
        ring]
    _ = ∫ w, J w ∂upperPeanoAdjacentRestSumLaw b i := by
      unfold upperPeanoAdjacentRestSumLaw
      have hrest : AEMeasurable restSum
          (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
        apply Continuous.aemeasurable
        dsimp [restSum]
        apply continuous_finsetSum
        intro j hj
        exact continuous_const.mul (continuous_apply j)
      rw [integral_map hrest hJ.aestronglyMeasurable]

/-- Immediately before a coordinate replacement, the selected coordinate is
Gaussian and the unchanged rest sum is outermost. -/
theorem upperPeanoHybridValue_split_before
    {m : ℕ} (b : Fin (m + 1) → ℝ) (s : ℂ) (i : Fin (m + 1))
    (hint : Integrable (fun x : Fin (m + 1) → ℝ =>
      complexQuadraticExp s (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw i.val))) :
    upperPeanoHybridValue b s i.val =
      ∫ w, ∫ y : ℝ, complexQuadraticExp s (w + b i * y)
        ∂gaussianReal 0 1 ∂upperPeanoAdjacentRestSumLaw b i :=
  (upperPeanoHybridValue_split_coordinate b s i i.val (gaussianReal 0 1)
    (upperPeanoHybridMeasure_before_map_piFinSuccAbove i) hint).1

/-- Immediately after a coordinate replacement, the selected coordinate is
Rademacher and the unchanged rest sum is outermost. -/
theorem upperPeanoHybridValue_split_after
    {m : ℕ} (b : Fin (m + 1) → ℝ) (s : ℂ) (i : Fin (m + 1))
    (hint : Integrable (fun x : Fin (m + 1) → ℝ =>
      complexQuadraticExp s (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw (i.val + 1)))) :
    upperPeanoHybridValue b s (i.val + 1) =
      ∫ w, ∫ y : ℝ, complexQuadraticExp s (w + b i * y)
        ∂standardRademacherMeasure ∂upperPeanoAdjacentRestSumLaw b i :=
  (upperPeanoHybridValue_split_coordinate b s i (i.val + 1)
    standardRademacherMeasure
    (upperPeanoHybridMeasure_after_map_piFinSuccAbove i) hint).1

/-- The concrete adjacent hybrid replacement supplies the exact `hfirst`
identity used by the fourth-order Peano telescope. -/
theorem upperPeanoHybridValue_adjacent_hfirst
    {m : ℕ} (b : Fin (m + 1) → ℝ) (s : ℂ) (i : Fin (m + 1))
    (hscale : 2 * b i ^ 2 * s.re < 1)
    (hbeforeInt : Integrable (fun x : Fin (m + 1) → ℝ =>
      complexQuadraticExp s (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw i.val)))
    (hafterInt : Integrable (fun x : Fin (m + 1) → ℝ =>
      complexQuadraticExp s (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw (i.val + 1)))) :
    upperPeanoHybridValue b s i.val -
        upperPeanoHybridValue b s (i.val + 1) =
      (b i ^ 4 / 12 : ℝ) •
        ∫ w, ∫ k : ℝ,
          iteratedDeriv 4 (complexQuadraticExp s) (w + b i * k)
            ∂peanoKMeasure ∂upperPeanoAdjacentRestSumLaw b i := by
  have hbefore := upperPeanoHybridValue_split_coordinate b s i i.val
    (gaussianReal 0 1) (upperPeanoHybridMeasure_before_map_piFinSuccAbove i)
      hbeforeInt
  have hafter := upperPeanoHybridValue_split_coordinate b s i (i.val + 1)
    standardRademacherMeasure
      (upperPeanoHybridMeasure_after_map_piFinSuccAbove i) hafterInt
  exact upperPeanoHybridValue_adjacent_fourthPeano b s i
    (upperPeanoAdjacentRestSumLaw b i) hscale hbefore.2 hafter.2
      hbefore.1 hafter.1

end CertifiedJL
