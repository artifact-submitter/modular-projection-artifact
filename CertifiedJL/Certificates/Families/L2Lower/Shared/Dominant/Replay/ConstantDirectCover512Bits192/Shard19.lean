import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover512Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard19

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192

open ConstantNumeric

private theorem shard19_row_caps :
    ConstantDirectCover128Shard19.entries.all (fun entry =>
      rowCapsCheck entry.cell entry.certificate) = true := by
  exact ConstantDirectCover128Shard19.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard19_target_certified :
    ConstantDirectCover128Shard19.entries.all (fun entry =>
      localTargetCheckFor 512 71 ((fun entry => entry.cell) entry)
        ((fun entry => entry.certificate) entry) budget) = true := by
  decide +kernel

theorem shard19_certified :
    ConstantDirectCover128Shard19.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 512 71
      ConstantDirectCover128Shard19.entries (fun entry => entry.cell)
      (fun entry => entry.certificate) budget shard19_row_caps
      shard19_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192
