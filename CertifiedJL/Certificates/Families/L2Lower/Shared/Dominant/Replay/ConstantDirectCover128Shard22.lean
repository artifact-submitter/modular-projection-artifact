-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard22

open ConstantNumeric

def cell88 : Cell where
  lower := 21 / 512
  upper := 11 / 256
  thresholdUpper := 2500 / 2401
  modulusLower := 611 / 200
  z := 47 / 20

def certificate88 : Certificate where
  inactiveUpper := 955477 / 1000000
  activeUpper := 14731 / 125000
  growthUpper := 6635368471505288969685169078272

def entry88 : Entry := ⟨cell88, certificate88⟩

def cell89 : Cell where
  lower := 1 / 4
  upper := 3 / 8
  thresholdUpper := 625 / 686
  modulusLower := 2651 / 1000
  z := 61 / 20

def certificate89 : Certificate where
  inactiveUpper := 768619 / 1000000
  activeUpper := 261943 / 1000000
  growthUpper := 100439423898243485854452492076580864

def entry89 : Entry := ⟨cell89, certificate89⟩

def cell90 : Cell where
  lower := 17 / 512
  upper := 9 / 256
  thresholdUpper := 79375 / 76832
  modulusLower := 3043 / 1000
  z := 12 / 5

def certificate90 : Certificate where
  inactiveUpper := 192561 / 200000
  activeUpper := 108463 / 1000000
  growthUpper := 17047975259552675936497588764672

def entry90 : Entry := ⟨cell90, certificate90⟩

def cell91 : Cell where
  lower := 7 / 512
  upper := 1 / 64
  thresholdUpper := 19375 / 19208
  modulusLower := 1503 / 500
  z := 27 / 10

def certificate91 : Certificate where
  inactiveUpper := 982391 / 1000000
  activeUpper := 14873 / 200000
  growthUpper := 20194402977801918489556263437860864

def entry91 : Entry := ⟨cell91, certificate91⟩

def entries : List Entry := [entry88, entry89, entry90, entry91]

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

end ConstantDirectCover128Shard22
end SparseThresholdDominant
end CertifiedJL
