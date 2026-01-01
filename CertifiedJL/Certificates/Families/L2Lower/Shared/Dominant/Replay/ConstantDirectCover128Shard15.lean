-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard15

open ConstantNumeric

def cell60 : Cell where
  lower := 15 / 1024
  upper := 1 / 64
  thresholdUpper := 311875 / 307328
  modulusLower := 3019 / 1000
  z := 53 / 20

def certificate60 : Certificate where
  inactiveUpper := 981489 / 1000000
  activeUpper := 77773 / 1000000
  growthUpper := 7475706103830454731143754704486400

def entry60 : Entry := ⟨cell60, certificate60⟩

def cell61 : Cell where
  lower := 5 / 256
  upper := 3 / 128
  thresholdUpper := 155625 / 153664
  modulusLower := 3013 / 1000
  z := 51 / 20

def certificate61 : Certificate where
  inactiveUpper := 61023 / 62500
  activeUpper := 44733 / 500000
  growthUpper := 339040165188461181891436804571136

def entry61 : Entry := ⟨cell61, certificate61⟩

def cell62 : Cell where
  lower := 23 / 1024
  upper := 3 / 128
  thresholdUpper := 5625 / 5488
  modulusLower := 1517 / 500
  z := 5 / 2

def certificate62 : Certificate where
  inactiveUpper := 243357 / 250000
  activeUpper := 93217 / 1000000
  growthUpper := 189096111593227172226989513768960

def entry62 : Entry := ⟨cell62, certificate62⟩

def cell63 : Cell where
  lower := 11 / 512
  upper := 3 / 128
  thresholdUpper := 156875 / 153664
  modulusLower := 121 / 40
  z := 51 / 20

def certificate63 : Certificate where
  inactiveUpper := 48703 / 50000
  activeUpper := 44633 / 500000
  growthUpper := 618733454942712423755006649303040

def entry63 : Entry := ⟨cell63, certificate63⟩

def entries : List Entry := [entry60, entry61, entry62, entry63]

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

end ConstantDirectCover128Shard15
end SparseThresholdDominant
end CertifiedJL
