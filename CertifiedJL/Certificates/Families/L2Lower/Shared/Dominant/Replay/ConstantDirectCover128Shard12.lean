-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard12

open ConstantNumeric

def cell48 : Cell where
  lower := 3 / 256
  upper := 7 / 512
  thresholdUpper := 19375 / 19208
  modulusLower := 1503 / 500
  z := 27 / 10

def certificate48 : Certificate where
  inactiveUpper := 984891 / 1000000
  activeUpper := 73459 / 1000000
  growthUpper := 20194402977801918489556263437860864

def entry48 : Entry := ⟨cell48, certificate48⟩

def cell49 : Cell where
  lower := 13 / 1024
  upper := 7 / 512
  thresholdUpper := 155625 / 153664
  modulusLower := 377 / 125
  z := 27 / 10

def certificate49 : Certificate where
  inactiveUpper := 196727 / 200000
  activeUpper := 73367 / 1000000
  growthUpper := 27767778595434399636472374725967872

def entry49 : Entry := ⟨cell49, certificate49⟩

def cell50 : Cell where
  lower := 7 / 256
  upper := 15 / 512
  thresholdUpper := 158125 / 153664
  modulusLower := 3037 / 1000
  z := 49 / 20

def certificate50 : Certificate where
  inactiveUpper := 968493 / 1000000
  activeUpper := 100693 / 1000000
  growthUpper := 57113529692850527089983320227840

def entry50 : Entry := ⟨cell50, certificate50⟩

def cell51 : Cell where
  lower := 11 / 1024
  upper := 3 / 256
  thresholdUpper := 44375 / 43904
  modulusLower := 3013 / 1000
  z := 13 / 4

def certificate51 : Certificate where
  inactiveUpper := 196667 / 200000
  activeUpper := 43407 / 1000000
  growthUpper := 237517467988009751535673953992175358312448

def entry51 : Entry := ⟨cell51, certificate51⟩

def entries : List Entry := [entry48, entry49, entry50, entry51]

theorem entries_valid : entriesValidCheck entries = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem entries_row_caps : entriesRowCapsCheck entries = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem entries_target_certified : entriesLocalTargetCheckAt entries
    (187 / (200 * 2 ^ 128)) = true := by
  decide +kernel

theorem entries_certified : entriesCertifiedCheckAt entries
    (187 / (200 * 2 ^ 128)) = true := by
  exact entriesCertifiedCheckAt_of_checks entries
    (187 / (200 * 2 ^ 128)) entries_row_caps entries_target_certified

end ConstantDirectCover128Shard12
end SparseThresholdDominant
end CertifiedJL
