-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard42

open ConstantNumeric

def cell168 : Cell where
  lower := 1 / 8
  upper := 1 / 4
  thresholdUpper := 1250 / 2401
  modulusLower := 2
  z := 21 / 4

def certificate168 : Certificate where
  inactiveUpper := 79923 / 100000
  activeUpper := 206769 / 1000000
  growthUpper := 26802379169318557748975668589232128

def entry168 : Entry := ⟨cell168, certificate168⟩

def cell169 : Cell where
  lower := 7 / 16
  upper := 1 / 2
  thresholdUpper := 3125 / 4802
  modulusLower := 459 / 200
  z := 81 / 20

def certificate169 : Certificate where
  inactiveUpper := 129713 / 200000
  activeUpper := 46031 / 125000
  growthUpper := 1580338287453406572044412575023104

def entry169 : Entry := ⟨cell169, certificate169⟩

def cell170 : Cell where
  lower := 5 / 16
  upper := 3 / 8
  thresholdUpper := 1250 / 2401
  modulusLower := 2
  z := 53 / 10

def certificate170 : Certificate where
  inactiveUpper := 41283 / 62500
  activeUpper := 339487 / 1000000
  growthUpper := 57018994707430806776593378147565568

def entry170 : Entry := ⟨cell170, certificate170⟩

def cell171 : Cell where
  lower := 1 / 32
  upper := 1 / 16
  thresholdUpper := 8125 / 9604
  modulusLower := 2651 / 1000
  z := 63 / 20

def certificate171 : Certificate where
  inactiveUpper := 954841 / 1000000
  activeUpper := 4557 / 62500
  growthUpper := 3694681852908290501161395421184000

def entry171 : Entry := ⟨cell171, certificate171⟩

def entries : List Entry := [entry168, entry169, entry170, entry171]

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

end ConstantDirectCover128Shard42
end SparseThresholdDominant
end CertifiedJL
