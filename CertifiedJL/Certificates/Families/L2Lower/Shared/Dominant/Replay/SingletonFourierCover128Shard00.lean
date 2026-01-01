import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128

namespace CertifiedJL.SparseThresholdDominant.SingletonFourierCover128

open SingletonFourierNumeric128

def shard00 : List Cell := [cell00, cell01, cell02, cell03, cell04]

set_option maxRecDepth 100000 in
theorem cell00_certified : certifiedCheck cell00 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell01_certified : certifiedCheck cell01 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell02_certified : certifiedCheck cell02 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell03_certified : certifiedCheck cell03 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell04_certified : certifiedCheck cell04 = true := by
  decide +kernel

theorem shard00_certified : shard00.all certifiedCheck = true := by
  simp [shard00, cell00_certified, cell01_certified, cell02_certified, cell03_certified, cell04_certified]

end CertifiedJL.SparseThresholdDominant.SingletonFourierCover128
