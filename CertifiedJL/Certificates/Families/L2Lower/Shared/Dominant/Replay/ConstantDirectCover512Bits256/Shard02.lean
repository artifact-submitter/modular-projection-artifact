import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover512Bits256.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard02

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits256

set_option maxRecDepth 100000 in
theorem shard02_certified :
    ConstantDirectCover128Shard02.entries.all targetCheckA = true := by
  decide +kernel

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits256
