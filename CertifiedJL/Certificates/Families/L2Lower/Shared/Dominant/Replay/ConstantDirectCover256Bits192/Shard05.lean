import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover256Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard05

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192

open ConstantNumeric

private theorem shard05_row_caps :
    ConstantDirectCover128Shard05.entries.all (fun entry =>
      rowCapsCheck entry.cell (targetCertificate entry)) = true := by
  exact all_rowCapsCheck_of_eq
    ConstantDirectCover128Shard05.entries (fun entry => entry.cell) targetCertificate
    (by decide +kernel) (by decide +kernel)
    ConstantDirectCover128Shard05.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard05_target_certified :
    ConstantDirectCover128Shard05.entries.all (fun entry =>
      localTargetCheckFor 256 9 ((fun entry => entry.cell) entry)
        (targetCertificate entry) budget) = true := by
  decide +kernel

theorem shard05_certified :
    ConstantDirectCover128Shard05.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 256 9
      ConstantDirectCover128Shard05.entries (fun entry => entry.cell)
      targetCertificate budget shard05_row_caps
      shard05_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192
