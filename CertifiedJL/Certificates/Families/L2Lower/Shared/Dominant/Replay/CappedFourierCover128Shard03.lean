import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover128

namespace CertifiedJL.SparseThresholdDominant.CappedFourierCover128

open CappedFourierNumeric128

def shard03 : List Cell := [cell12, cell13, cell14, cell15]

set_option maxRecDepth 100000 in
theorem cell12_certified : certifiedCheck cell12 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem cell13_certified : certifiedCheck cell13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell14_certified : certifiedCheck cell14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem cell15_certified : certifiedCheck cell15 = true := by decide +kernel
theorem shard03_certified : shard03.all certifiedCheck = true := by
  simp [shard03, cell12_certified, cell13_certified,
    cell14_certified, cell15_certified]

end CertifiedJL.SparseThresholdDominant.CappedFourierCover128
