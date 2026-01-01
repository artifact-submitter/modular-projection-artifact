import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover192Bits128.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard14

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover192Bits128

open ConstantNumeric

private theorem shard14_row_caps :
    ConstantDirectCover128Shard14.entries.all (fun entry =>
      rowCapsCheck (retargetEntry entry).cell
        (retargetEntry entry).certificate) = true := by
  exact all_rowCapsCheck_of_eq
    ConstantDirectCover128Shard14.entries (fun entry => (retargetEntry entry).cell)
    (fun entry => (retargetEntry entry).certificate)
    (by decide +kernel) (by decide +kernel)
    ConstantDirectCover128Shard14.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard14_target_certified :
    ConstantDirectCover128Shard14.entries.all (fun entry =>
      localTargetCheckFor 192 12 ((fun entry => (retargetEntry entry).cell) entry)
        ((fun entry => (retargetEntry entry).certificate) entry) budget) = true := by
  decide +kernel

theorem shard14_certified :
    ConstantDirectCover128Shard14.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 192 12
      ConstantDirectCover128Shard14.entries (fun entry => (retargetEntry entry).cell)
      (fun entry => (retargetEntry entry).certificate) budget shard14_row_caps
      shard14_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover192Bits128
