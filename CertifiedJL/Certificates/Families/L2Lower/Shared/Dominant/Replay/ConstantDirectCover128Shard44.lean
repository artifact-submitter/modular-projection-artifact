-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard44

open ConstantNumeric

def cell176 : Cell where
  lower := 3 / 16
  upper := 1 / 4
  thresholdUpper := 625 / 686
  modulusLower := 2651 / 1000
  z := 16 / 5

def certificate176 : Certificate where
  inactiveUpper := 797349 / 1000000
  activeUpper := 7083 / 40000
  growthUpper := 5285630643895111479137726347677270016

def entry176 : Entry := ⟨cell176, certificate176⟩

def cell177 : Cell where
  lower := 0
  upper := 1 / 8
  thresholdUpper := 1875 / 4802
  modulusLower := 2
  z := 49 / 10

def certificate177 : Certificate where
  inactiveUpper := 200921 / 200000
  activeUpper := 95989 / 1000000
  growthUpper := 1261879121873642043998208

def entry177 : Entry := ⟨cell177, certificate177⟩

def cell178 : Cell where
  lower := 0
  upper := 1 / 16
  thresholdUpper := 1250 / 2401
  modulusLower := 2
  z := 61 / 10

def certificate178 : Certificate where
  inactiveUpper := 1001777 / 1000000
  activeUpper := 12179 / 500000
  growthUpper := 10035959598892545849371358289579762253824

def entry178 : Entry := ⟨cell178, certificate178⟩

def cell179 : Cell where
  lower := 1 / 16
  upper := 1 / 8
  thresholdUpper := 3125 / 4802
  modulusLower := 541 / 250
  z := 89 / 20

def certificate179 : Certificate where
  inactiveUpper := 17757 / 20000
  activeUpper := 1223 / 15625
  growthUpper := 3000627980652483742290814970974175232

def entry179 : Entry := ⟨cell179, certificate179⟩

def entries : List Entry := [entry176, entry177, entry178, entry179]

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

end ConstantDirectCover128Shard44
end SparseThresholdDominant
end CertifiedJL
