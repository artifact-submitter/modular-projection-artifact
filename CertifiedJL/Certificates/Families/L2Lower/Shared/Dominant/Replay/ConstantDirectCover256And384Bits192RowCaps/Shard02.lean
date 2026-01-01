/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover256And384Bits192Caps

/-! # Shared replay of the tightened 256/192 and 384/192 row cap in shard 02 -/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover256And384Bits192Caps

open ConstantNumeric

set_option maxRecDepth 100000 in
theorem shard02_row_caps :
    ConstantDirectCover128Shard02.entries.all (fun entry =>
      rowCapsCheck entry.cell (targetCertificate entry)) = true := by
  decide +kernel

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover256And384Bits192Caps
