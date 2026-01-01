/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Core

/-! # Semantic certificate contract for the sparse upper tail -/

namespace CertifiedJL.CertificateContracts

/-- Exact semantic output consumed from the centered-hybrid low-profile replay.
The independent high-profile endpoint is a small kernel arithmetic check and
therefore does not belong to the expensive certificate boundary. -/
def SparseL2UpperHybrid : Prop :=
  ∀ certificate ∈ SparseUpperHybrid.certificateBoxes,
    (SparseUpperHybrid.certificateBound certificate).upperRat < 1 ∧
      (∀ segment ∈ certificate.segments, ∀ i < segment.count,
        SparseUpperHybrid.hybridCellSideCheck certificate.box segment i = true) ∧
      (SparseUpperHybrid.finiteIntegralFrom
        ((SparseUpperHybrid.certificateChunkPlan certificate).map
          (SparseUpperHybrid.certificateChunkValue certificate)) +
        SparseUpperHybrid.tail certificate.box).lo = 0

end CertifiedJL.CertificateContracts
