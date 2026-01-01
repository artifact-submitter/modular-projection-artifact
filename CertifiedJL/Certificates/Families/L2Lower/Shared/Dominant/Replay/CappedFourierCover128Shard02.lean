import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover128

namespace CertifiedJL.SparseThresholdDominant.CappedFourierCover128

open CappedFourierNumeric128

def shard02 : List Cell := [cell08, cell09, cell10, cell11]

set_option maxRecDepth 100000 in
theorem cell08_certified : certifiedCheck cell08 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem cell09_certified : certifiedCheck cell09 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell10_certified : certifiedCheck cell10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell11_certified : certifiedCheck cell11 = true := by decide +kernel
theorem shard02_certified : shard02.all certifiedCheck = true := by
  simp [shard02, cell08_certified, cell09_certified,
    cell10_certified, cell11_certified]

end CertifiedJL.SparseThresholdDominant.CappedFourierCover128
