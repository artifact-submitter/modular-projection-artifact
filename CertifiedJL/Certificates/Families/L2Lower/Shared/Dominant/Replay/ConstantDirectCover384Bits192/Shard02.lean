import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover384Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard02
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover256And384Bits192RowCaps.Shard02

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover384Bits192

open ConstantNumeric

private theorem shard02_row_caps :
    ConstantDirectCover128Shard02.entries.all (fun entry =>
      rowCapsCheck entry.cell (targetCertificate entry)) = true := by
  exact ConstantDirectCover256And384Bits192Caps.shard02_row_caps

set_option maxRecDepth 100000 in
private theorem shard02_target_certified :
    ConstantDirectCover128Shard02.entries.all (fun entry =>
      localTargetCheckFor 384 43 ((fun entry => entry.cell) entry)
        (targetCertificate entry) budget) = true := by
  decide +kernel

theorem shard02_certified :
    ConstantDirectCover128Shard02.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 384 43
      ConstantDirectCover128Shard02.entries (fun entry => entry.cell)
      targetCertificate budget shard02_row_caps
      shard02_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover384Bits192
