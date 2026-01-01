/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.ConditioningLower

/-! # Canaries for lower bounds through finite conditioning -/

namespace CertifiedJL.Probability

example : (1 / 2 : ℝ) ≤
    (eventProbability
      ((PMF.uniformOfFintype (Bool × Bool)).map fun x => (x.1, x.2))
      (fun x => x.2 = true)).toReal := by
  apply eventProbability_map_uniform_prod_toReal_ge
  intro a
  rw [show eventProbability
      ((PMF.uniformOfFintype Bool).map (fun b => (a, b)))
        (fun x => x.2 = true) =
      eventProbability (PMF.uniformOfFintype Bool) (fun b => b = true) by
    unfold eventProbability
    rw [PMF.map_comp]
    rfl]
  norm_num [eventProbability_uniform_eq_card]

#print axioms eventProbability_map_uniform_prod_toReal_ge_average
#print axioms eventProbability_map_uniform_prod_toReal_ge

end CertifiedJL.Probability
