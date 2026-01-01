/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.Transport.ParameterMonotonicity
import CertifiedJL.Statements.Transport.Rows

/-! # API canaries for row and parameter transports -/

namespace CertifiedJL.Tests.RowTransports

example (d : ℕ) :
    (ProjectionDistribution.balancedTernary.matrixPMF 5 d).map
        (restrictRows (by omega : 2 ≤ 5)) =
      ProjectionDistribution.balancedTernary.matrixPMF 2 d :=
  ProjectionDistribution.matrixPMF_map_restrictRows _ (by omega)

example {d q : ℕ} (J : Fin 5 → Fin d → ℤ) (w : Fin d → ℤ) :
    modularProjectionSqNorm q (restrictRows (by omega : 2 ≤ 5) J) w ≤
      modularProjectionSqNorm q J w :=
  modularProjectionSqNorm_restrictRows_le (by omega) J w

example {distribution : ProjectionDistribution} {rows : ℕ} {modulusMargin : NonnegativeRatio}
    {budget : ENNReal}
    (h : L2ThresholdLowerTailAt
      { distribution := distribution, rows := rows, squaredNormFloor := NonnegativeRatio.ofNat 2,
        modulusMargin := modulusMargin } budget) :
    L2ThresholdLowerTailAt
      { distribution := distribution, rows := rows, squaredNormFloor := NonnegativeRatio.ofNat 1,
        modulusMargin := modulusMargin } budget := by
  apply h.mono_squaredNormFloor
  simp [NonnegativeRatio.LE, NonnegativeRatio.ofNat]

example {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    {coordinateCap : NonnegativeRatio}
    (hcap : coordinateCap.LE parameters.coordinateCap)
    (h : AffineLInfThresholdLowerTailAt parameters budget) :
    AffineLInfThresholdLowerTailAt
      { parameters with coordinateCap := coordinateCap } budget :=
  h.mono_coordinateCap hcap.squaredLE

example {distribution : ProjectionDistribution} {squaredNormFloor modulusMargin : NonnegativeRatio}
    {budget : ENNReal}
    (h : AffineL2ThresholdLowerTailAt
      { distribution := distribution, rows := 2, squaredNormFloor := squaredNormFloor,
        modulusMargin := modulusMargin } budget) :
    AffineL2ThresholdLowerTailAt
      { distribution := distribution, rows := 5, squaredNormFloor := squaredNormFloor,
        modulusMargin := modulusMargin } budget :=
  h.extend_rows (by omega)

#print axioms CertifiedJL.sparseRademacherMatrix_map_restrictRows
#print axioms CertifiedJL.L2UpperTailAt.restrict_rows
#print axioms CertifiedJL.AffineL2ThresholdLowerTailAt.extend_rows

end CertifiedJL.Tests.RowTransports
