/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Spec
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Verified

/-! # Kernel-verified provider for the sparse upper-tail contract -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2UpperHybrid_verified :
    CertificateContracts.SparseL2UpperHybrid := by
  intro certificate hcertificate
  exact ⟨SparseUpperHybrid.certificate_upperRat_lt_one hcertificate,
    SparseUpperHybrid.certificate_sideChecks hcertificate,
    SparseUpperHybrid.certificate_finiteTail_lo_eq_zero hcertificate⟩

end CertifiedJL.CertificateProviders
