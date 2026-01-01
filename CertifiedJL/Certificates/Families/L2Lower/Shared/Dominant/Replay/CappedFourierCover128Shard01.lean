import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover128

namespace CertifiedJL.SparseThresholdDominant.CappedFourierCover128

open CappedFourierNumeric128

def shard01 : List Cell := [cell04, cell05, cell06, cell07]

set_option maxRecDepth 100000 in
theorem cell04_certified : certifiedCheck cell04 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem cell05_certified : certifiedCheck cell05 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell06_certified : certifiedCheck cell06 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell07_certified : certifiedCheck cell07 = true := by decide +kernel
theorem shard01_certified : shard01.all certifiedCheck = true := by
  simp [shard01, cell04_certified, cell05_certified,
    cell06_certified, cell07_certified]

end CertifiedJL.SparseThresholdDominant.CappedFourierCover128
