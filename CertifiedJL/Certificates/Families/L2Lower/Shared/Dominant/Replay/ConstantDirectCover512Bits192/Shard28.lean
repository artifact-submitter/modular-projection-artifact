import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover512Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard28

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192

open ConstantNumeric

private theorem shard28_row_caps :
    ConstantDirectCover128Shard28.entries.all (fun entry =>
      rowCapsCheck entry.cell entry.certificate) = true := by
  exact ConstantDirectCover128Shard28.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard28_target_certified :
    ConstantDirectCover128Shard28.entries.all (fun entry =>
      localTargetCheckFor 512 71 ((fun entry => entry.cell) entry)
        ((fun entry => entry.certificate) entry) budget) = true := by
  decide +kernel

theorem shard28_certified :
    ConstantDirectCover128Shard28.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 512 71
      ConstantDirectCover128Shard28.entries (fun entry => entry.cell)
      (fun entry => entry.certificate) budget shard28_row_caps
      shard28_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192
