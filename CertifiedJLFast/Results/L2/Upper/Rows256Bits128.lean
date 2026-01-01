/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Assembly
import CertifiedJLFast.Assumptions.Families.OneRow975
import CertifiedJLFast.Assumptions.Families.L2Upper.Rows256Bits128

/-! # Assumption-backed 256-row result specializations -/

namespace CertifiedJLFast.Results.L2.Upper.Rows256Bits128

/-- Balanced-ternary upper tail at threshold `338`. -/
theorem ternaryL2Upper338 :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := CertifiedJL.NonnegativeRatio.ofNat 338 }
      (CertifiedJL.failureTarget 128) := by
  intro q d w
  simp only [CertifiedJL.ProjectionDistribution.matrixPMF_balancedTernary]
  rw [CertifiedJL.eventProbability_congr
    (CertifiedJL.sparseRademacherMatrix 256 d)
    (event' := CertifiedJL.SparseUpperFailure q w) (by
      intro J
      simp [CertifiedJL.L2UpperFailure, CertifiedJL.SparseUpperFailure,
        CertifiedJL.NonnegativeRatio.ofNat, CertifiedJL.sparseUpperThreshold])]
  exact (CertifiedJL.CertificateAssembly.sparseL2Upper128
    Assumptions.sparse_l2_upper_hybrid_assumed) q d w

end CertifiedJLFast.Results.L2.Upper.Rows256Bits128
