/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.SparseUpperContourFamilyFixture
import CertifiedJL.Arithmetic.Interval.Interval

/-! Raw generated endpoints for upper-contour family box 1. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01

set_option linter.style.longLine false

def chunks : List (Interval (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).precision) :=
  [
    ⟨0,
      412316860418⟩,
    ⟨0,
      710056015441⟩,
    ⟨0,
      265508611974⟩
  ]

def expectedBound : Interval (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).precision :=
  ⟨0,
      20⟩

end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01
