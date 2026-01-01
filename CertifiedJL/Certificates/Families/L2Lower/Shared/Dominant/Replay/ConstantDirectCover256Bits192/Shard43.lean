import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover256Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard43

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192

open ConstantNumeric

private theorem shard43_row_caps :
    ConstantDirectCover128Shard43.entries.all (fun entry =>
      rowCapsCheck entry.cell (targetCertificate entry)) = true := by
  exact all_rowCapsCheck_of_eq
    ConstantDirectCover128Shard43.entries (fun entry => entry.cell) targetCertificate
    (by decide +kernel) (by decide +kernel)
    ConstantDirectCover128Shard43.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard43_target_certified :
    ConstantDirectCover128Shard43.entries.all (fun entry =>
      localTargetCheckFor 256 9 ((fun entry => entry.cell) entry)
        (targetCertificate entry) budget) = true := by
  decide +kernel

theorem shard43_certified :
    ConstantDirectCover128Shard43.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 256 9
      ConstantDirectCover128Shard43.entries (fun entry => entry.cell)
      targetCertificate budget shard43_row_caps
      shard43_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192
