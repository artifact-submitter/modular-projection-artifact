/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover512Floor73Bits193.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard28

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Floor73Bits193

open ConstantNumeric

set_option maxRecDepth 100000 in
private theorem shard28_target_certified :
    ConstantDirectCover128Shard28.entries.all (fun entry =>
      localTargetCheckFor 512 73 entry.cell entry.certificate budget) = true := by
  decide +kernel

theorem shard28_certified :
    ConstantDirectCover128Shard28.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 512 73
      ConstantDirectCover128Shard28.entries (fun entry => entry.cell)
      (fun entry => entry.certificate) budget
      ConstantDirectCover128Shard28.entries_row_caps
      shard28_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Floor73Bits193
