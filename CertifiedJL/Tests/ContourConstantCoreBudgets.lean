/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box14
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box15
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box16
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.GaussianCoreAssembly

/-! Cheap exact endpoint feasibility for a constant-cap core replacement.
These checks do not certify the retained numerical suffix or prove its
semantic assembly. They do not import any expensive replay module. -/

namespace CertifiedJL.SparseUpperContourFamily.ConstantCoreExperiment

open Instances.Rows384Bits192Threshold509
open CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509

def replacementBound (index removedChunks : ℕ) (cutoff : ℚ)
    (chunks : List (Interval parameters.precision)) : Interval parameters.precision :=
  let box := profileBoxes.getD index default
  boxPrefactor parameters box *
    boxIntegralFrom parameters box
      (constantCapCoreUpper parameters box cutoff :: chunks.drop removedChunks)

set_option maxRecDepth 100000 in
/-- The selected suffixes cover exactly the interval after each replaced core. -/
theorem three_suffix_geometries :
    retainedSuffixGeometryCheck (profileBoxes.getD 14 default) (1 / 12)
      ((boxChunkPlan (profileBoxes.getD 14 default)).drop 1) = true ∧
    retainedSuffixGeometryCheck (profileBoxes.getD 15 default) (1 / 4)
      ((boxChunkPlan (profileBoxes.getD 15 default)).drop 3) = true ∧
    retainedSuffixGeometryCheck (profileBoxes.getD 16 default) (2 / 3)
      ((boxChunkPlan (profileBoxes.getD 16 default)).drop 7) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1024 in
theorem three_original_targets :
    Interval.upperLTCheck (replacementBound 14 1 (1 / 12) Box14.chunks) 1 = true ∧
    Interval.upperLTCheck (replacementBound 15 3 (1 / 4) Box15.chunks) 1 = true ∧
    Interval.upperLTCheck (replacementBound 16 7 (2 / 3) Box16.chunks) 1 = true := by
  decide +kernel

end CertifiedJL.SparseUpperContourFamily.ConstantCoreExperiment
