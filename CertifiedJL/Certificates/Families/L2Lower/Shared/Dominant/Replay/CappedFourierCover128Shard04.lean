import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover128

namespace CertifiedJL.SparseThresholdDominant.CappedFourierCover128

open CappedFourierNumeric128

def shard04 : List Cell := [cell16, cell17, cell18, cell19]

set_option maxRecDepth 100000 in
theorem cell16_certified : certifiedCheck cell16 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem cell17_certified : certifiedCheck cell17 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell18_certified : certifiedCheck cell18 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell19_certified : certifiedCheck cell19 = true := by decide +kernel
theorem shard04_certified : shard04.all certifiedCheck = true := by
  simp [shard04, cell16_certified, cell17_certified,
    cell18_certified, cell19_certified]

end CertifiedJL.SparseThresholdDominant.CappedFourierCover128
