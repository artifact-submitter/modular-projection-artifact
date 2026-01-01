import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover512Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard03

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192

open ConstantNumeric

private theorem shard03_row_caps :
    ConstantDirectCover128Shard03.entries.all (fun entry =>
      rowCapsCheck entry.cell entry.certificate) = true := by
  exact ConstantDirectCover128Shard03.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard03_target_certified :
    ConstantDirectCover128Shard03.entries.all (fun entry =>
      localTargetCheckFor 512 71 ((fun entry => entry.cell) entry)
        ((fun entry => entry.certificate) entry) budget) = true := by
  decide +kernel

theorem shard03_certified :
    ConstantDirectCover128Shard03.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 512 71
      ConstantDirectCover128Shard03.entries (fun entry => entry.cell)
      (fun entry => entry.certificate) budget shard03_row_caps
      shard03_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192
