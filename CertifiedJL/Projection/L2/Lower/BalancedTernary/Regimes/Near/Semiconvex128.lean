/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.Convex.Deriv
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordSoundness128

/-! # Semiconvex interpolation for the high-Holder near band

The numerical certificate only has to check fixed Holder endpoints.  A uniform
lower bound on the second derivative transports those endpoint bounds across
each interval, with the sharp elementary secant defect `M * (u - l)^2 / 8`.
-/

namespace CertifiedJL
namespace ThresholdNearChord128

open Set

/-- A lower bound `f'' >= -M` controls the gap between `f` and the larger
endpoint value on an interval.  The derivative witnesses are kept explicit so
the result can be consumed without reasoning about `deriv` at the endpoints. -/
theorem le_max_endpoints_add_semiconvex_defect
    {f f' f'' : ℝ → ℝ} {l u y M : ℝ}
    (hlu : l < u) (hy : y ∈ Icc l u) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc l u))
    (hf' : ∀ z ∈ Ioo l u, HasDerivAt f (f' z) z)
    (hf'' : ∀ z ∈ Ioo l u, HasDerivAt f' (f'' z) z)
    (hcurv : ∀ z ∈ Ioo l u, -M ≤ f'' z) :
    f y ≤ max (f l) (f u) + M * (u - l) ^ 2 / 8 := by
  let g : ℝ → ℝ := fun z ↦ f z + (M / 2) * (z - l) * (z - u)
  let g' : ℝ → ℝ := fun z ↦
    f' z + (M / 2) * (z - u) + (M / 2) * (z - l)
  let g'' : ℝ → ℝ := fun z ↦ f'' z + M
  have hg : ContinuousOn g (Icc l u) := by
    apply hf.add
    fun_prop
  have hg' : ∀ z ∈ interior (Icc l u),
      HasDerivWithinAt g (g' z) (interior (Icc l u)) z := by
    intro z hz
    rw [interior_Icc] at hz ⊢
    change HasDerivWithinAt
      (fun z ↦ f z + (M / 2) * (z - l) * (z - u))
      (f' z + (M / 2) * (z - u) + (M / 2) * (z - l)) (Ioo l u) z
    convert (((hf' z hz).add
      (((hasDerivAt_id z).sub_const l).const_mul (M / 2) |>.mul
        ((hasDerivAt_id z).sub_const u))).hasDerivWithinAt) using 1
    all_goals try rfl
    simp only [id_eq, mul_one]
    ring
  have hg'' : ∀ z ∈ interior (Icc l u),
      HasDerivWithinAt g' (g'' z) (interior (Icc l u)) z := by
    intro z hz
    rw [interior_Icc] at hz ⊢
    change HasDerivWithinAt
      (fun z ↦ f' z + (M / 2) * (z - u) + (M / 2) * (z - l))
      (f'' z + M) (Ioo l u) z
    convert ((((hf'' z hz).add
      ((hasDerivAt_id z).sub_const u |>.const_mul (M / 2))).add
      ((hasDerivAt_id z).sub_const l |>.const_mul (M / 2))).hasDerivWithinAt) using 1
    all_goals try rfl
    simp only [mul_one]
    ring
  have hgcurv : ∀ z ∈ interior (Icc l u), 0 ≤ g'' z := by
    intro z hz
    rw [interior_Icc] at hz
    dsimp [g'']
    linarith [hcurv z hz]
  have hgconvex : ConvexOn ℝ (Icc l u) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l u) hg hg' hg'' hgcurv
  have hyseg : y ∈ segment ℝ l u := by
    rw [segment_eq_uIcc, uIcc_of_le hlu.le]
    exact hy
  have hgle : g y ≤ max (g l) (g u) :=
    hgconvex.le_on_segment (left_mem_Icc.mpr hlu.le) (right_mem_Icc.mpr hlu.le) hyseg
  have hquad : (y - l) * (u - y) ≤ (u - l) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((u + l) / 2 - y)]
  have hdefect : (M / 2) * ((y - l) * (u - y)) ≤ M * (u - l) ^ 2 / 8 := by
    nlinarith
  dsimp [g] at hgle
  simp only [sub_self, zero_mul, mul_zero, add_zero] at hgle
  calc
    f y = (f y + (M / 2) * (y - l) * (y - u)) +
        (M / 2) * ((y - l) * (u - y)) := by ring
    _ ≤ max (f l) (f u) + (M / 2) * ((y - l) * (u - y)) := by gcongr
    _ ≤ max (f l) (f u) + M * (u - l) ^ 2 / 8 := by gcongr

end ThresholdNearChord128
end CertifiedJL
