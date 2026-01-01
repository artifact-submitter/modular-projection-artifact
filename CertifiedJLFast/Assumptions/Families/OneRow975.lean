/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Spec

/-! # Assumption-backed providers for one-row certificate replay -/

namespace CertifiedJLFast.Assumptions

axiom moderate_grid_assumed :
  CertifiedJL.CertificateContracts.ModerateGrid

axiom sparse_one_row_envelope_assumed :
  CertifiedJL.CertificateContracts.SparseOneRowEnvelope

end CertifiedJLFast.Assumptions
