/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Data.ENNReal.Basic

/-!
# Power-of-two failure budgets

This module defines the primitive probability target shared by public theorem
statements and finite budget-allocation lemmas.
-/

namespace CertifiedJL

/-- The exact failure-probability target `2⁻ᵇ` for `bits = b`. -/
noncomputable def failureTarget (bits : ℕ) : ENNReal :=
  (2 : ENNReal)⁻¹ ^ bits

end CertifiedJL
