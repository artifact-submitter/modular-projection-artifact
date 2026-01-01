/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Assembly
import CertifiedJL.Certificates.Families.OneRow975.Provider
import CertifiedJL.Statements.OneRow.Upper

/-!
# Internal balanced-ternary one-row upper-tail ingredient at 141 bits

This module packages the coefficient-uniform one-row certificate used to
derive the advertised 256-row infinity-norm bound. Its declaration is
intentionally unsupported and uncataloged as a public result, even though the
256-row umbrella imports it transitively; the supported frontier starts at
192 rows.
-/

namespace CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform

/-- A balanced-ternary row exceeds `39/4` times the input norm with
probability strictly below `2⁻¹⁴¹`. This is an internal ingredient for the
256-row matrix theorem, not a separately advertised frontier endpoint. -/
theorem ternaryUpper39Over4 :
    OneRowUpperTailAt
      { distribution := .balancedTernary, threshold := 39 / 4 }
      (failureTarget 141) := by
  intro d w
  change eventProbability (sparseRademacherRow d)
    (fun row => |euclideanRowDot row w| > (39 / 4 : ℝ) * ‖w‖) <
      failureTarget 141
  rw [eventProbability_congr (sparseRademacherRow d)
    (event' := SparseOneRow975Event w) (by intro row; rfl)]
  simpa [sparseOneRowSecurityBits, failureTarget] using
    CertificateAssembly.sparseOneRow975
      CertificateProviders.moderateGrid_verified
      CertificateProviders.sparseOneRowEnvelope_verified d w

end CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform
