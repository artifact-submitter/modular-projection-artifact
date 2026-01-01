import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128

namespace CertifiedJL.SparseThresholdDominant.SingletonFourierCover128

open SingletonFourierNumeric128

def shard01 : List Cell := [cell05, cell06, cell07, cell08, cell09]

set_option maxRecDepth 100000 in
theorem cell05_certified : certifiedCheck cell05 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell06_certified : certifiedCheck cell06 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell07_certified : certifiedCheck cell07 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell08_certified : certifiedCheck cell08 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell09_certified : certifiedCheck cell09 = true := by
  decide +kernel

theorem shard01_certified : shard01.all certifiedCheck = true := by
  simp [shard01, cell05_certified, cell06_certified, cell07_certified, cell08_certified, cell09_certified]

end CertifiedJL.SparseThresholdDominant.SingletonFourierCover128
