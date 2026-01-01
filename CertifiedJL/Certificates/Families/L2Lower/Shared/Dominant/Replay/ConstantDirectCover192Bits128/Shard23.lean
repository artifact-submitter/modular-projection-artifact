import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover192Bits128.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard23

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover192Bits128

open ConstantNumeric

private theorem shard23_row_caps :
    ConstantDirectCover128Shard23.entries.all (fun entry =>
      rowCapsCheck (retargetEntry entry).cell
        (retargetEntry entry).certificate) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem shard23_target_certified :
    ConstantDirectCover128Shard23.entries.all (fun entry =>
      localTargetCheckFor 192 12 ((fun entry => (retargetEntry entry).cell) entry)
        ((fun entry => (retargetEntry entry).certificate) entry) budget) = true := by
  decide +kernel

theorem shard23_certified :
    ConstantDirectCover128Shard23.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 192 12
      ConstantDirectCover128Shard23.entries (fun entry => (retargetEntry entry).cell)
      (fun entry => (retargetEntry entry).certificate) budget shard23_row_caps
      shard23_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover192Bits128
