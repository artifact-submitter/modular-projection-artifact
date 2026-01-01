import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover384Bits192.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard19

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover384Bits192

open ConstantNumeric

private theorem shard19_row_caps :
    ConstantDirectCover128Shard19.entries.all (fun entry =>
      rowCapsCheck entry.cell (targetCertificate entry)) = true := by
  exact all_rowCapsCheck_of_eq
    ConstantDirectCover128Shard19.entries (fun entry => entry.cell) targetCertificate
    (by decide +kernel) (by decide +kernel)
    ConstantDirectCover128Shard19.entries_row_caps

set_option maxRecDepth 100000 in
private theorem shard19_target_certified :
    ConstantDirectCover128Shard19.entries.all (fun entry =>
      localTargetCheckFor 384 43 ((fun entry => entry.cell) entry)
        (targetCertificate entry) budget) = true := by
  decide +kernel

theorem shard19_certified :
    ConstantDirectCover128Shard19.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 384 43
      ConstantDirectCover128Shard19.entries (fun entry => entry.cell)
      targetCertificate budget shard19_row_caps
      shard19_target_certified

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover384Bits192
