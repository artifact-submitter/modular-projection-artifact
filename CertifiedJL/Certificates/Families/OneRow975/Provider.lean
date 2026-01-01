/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Spec
import CertifiedJL.Certificates.Families.OneRow975.Finite.Soundness
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Replay.CertificateProofs

/-! # Kernel-verified providers for the one-row certificate contracts -/

namespace CertifiedJL.CertificateProviders

theorem moderateGrid_verified : CertificateContracts.ModerateGrid :=
  TyurinModerate.moderateGridCells_certified

theorem sparseOneRowEnvelope_verified :
    CertificateContracts.SparseOneRowEnvelope :=
  fun y hy hy' =>
    SparseOneRowCertificate.scalarEnvelope_lt_target_of_le_certifiedProfileUpper
      (y := y) hy hy'

end CertifiedJL.CertificateProviders
