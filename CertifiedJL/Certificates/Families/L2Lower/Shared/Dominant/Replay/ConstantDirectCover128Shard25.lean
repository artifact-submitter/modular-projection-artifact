-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard25

open ConstantNumeric

def cell100 : Cell where
  lower := 9 / 512
  upper := 5 / 256
  thresholdUpper := 155625 / 153664
  modulusLower := 3013 / 1000
  z := 13 / 5

def certificate100 : Certificate where
  inactiveUpper := 978267 / 1000000
  activeUpper := 10429 / 125000
  growthUpper := 1472361592020440463212615588380672

def entry100 : Entry := ⟨cell100, certificate100⟩

def cell101 : Cell where
  lower := 1 / 64
  upper := 3 / 128
  thresholdUpper := 38125 / 38416
  modulusLower := 741 / 250
  z := 51 / 20

def certificate101 : Certificate where
  inactiveUpper := 122629 / 125000
  activeUpper := 89889 / 1000000
  growthUpper := 75356380601786489165928783151104

def entry101 : Entry := ⟨cell101, certificate101⟩

def cell102 : Cell where
  lower := 3 / 32
  upper := 1 / 8
  thresholdUpper := 2500 / 2401
  modulusLower := 741 / 250
  z := 5 / 2

def certificate102 : Certificate where
  inactiveUpper := 901247 / 1000000
  activeUpper := 149703 / 1000000
  growthUpper := 615095146915185183479979220926464

def entry102 : Entry := ⟨cell102, certificate102⟩

def cell103 : Cell where
  lower := 5 / 256
  upper := 3 / 128
  thresholdUpper := 19375 / 19208
  modulusLower := 3
  z := 51 / 20

def certificate103 : Certificate where
  inactiveUpper := 61023 / 62500
  activeUpper := 44737 / 500000
  growthUpper := 250971800846825797083009973747712

def entry103 : Entry := ⟨cell103, certificate103⟩

def entries : List Entry := [entry100, entry101, entry102, entry103]

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

end ConstantDirectCover128Shard25
end SparseThresholdDominant
end CertifiedJL
