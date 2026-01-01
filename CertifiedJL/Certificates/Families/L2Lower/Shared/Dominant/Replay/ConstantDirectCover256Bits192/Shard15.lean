import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover256Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard15

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192

open ConstantNumeric

private theorem shard15_row_caps :
    ConstantDirectCover128Shard15.entries.all (fun entry =>
      rowCapsCheck entry.cell (targetCertificate entry)) = true := by
  exact all_rowCapsCheck_of_eq
    ConstantDirectCover128Shard15.entries (fun entry => entry.cell) targetCertificate
    (by decide +kernel) (by decide +kernel)
    ConstantDirectCover128Shard15.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard15_target_certified :
    ConstantDirectCover128Shard15.entries.all (fun entry =>
      localTargetCheckFor 256 9 ((fun entry => entry.cell) entry)
        (targetCertificate entry) budget) = true := by
  decide +kernel

theorem shard15_certified :
    ConstantDirectCover128Shard15.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 256 9
      ConstantDirectCover128Shard15.entries (fun entry => entry.cell)
      targetCertificate budget shard15_row_caps
      shard15_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192
