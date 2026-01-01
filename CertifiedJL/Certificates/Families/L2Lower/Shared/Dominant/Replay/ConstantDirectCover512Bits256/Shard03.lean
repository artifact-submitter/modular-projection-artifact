import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover512Bits256.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard03

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits256

open ConstantNumeric
open SparseThresholdDominant.Numeric

set_option maxRecDepth 100000 in
theorem shard03_certified :
    ConstantDirectCover128Shard03.entries.all targetCheckA = true := by
  decide +kernel

/-- The extra half-cell introduced by splitting inherited cell 14 is sampled
alongside the shard containing the first half. -/
theorem cell14B_certified :
    localCertifiedCheckFor 512 57 cell14B (exactCertificate cell14B) budget = true := by
  set_option maxRecDepth 100000 in
    decide +kernel

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits256
