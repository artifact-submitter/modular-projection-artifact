-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard07

open ConstantNumeric

def cell28 : Cell where
  lower := 5 / 128
  upper := 11 / 256
  thresholdUpper := 159375 / 153664
  modulusLower := 3049 / 1000
  z := 47 / 20

def certificate28 : Certificate where
  inactiveUpper := 957483 / 1000000
  activeUpper := 118073 / 1000000
  growthUpper := 5029027551401883270861144719360

def entry28 : Entry := ⟨cell28, certificate28⟩

def cell29 : Cell where
  lower := 9 / 256
  upper := 5 / 128
  thresholdUpper := 79375 / 76832
  modulusLower := 3037 / 1000
  z := 12 / 5

def certificate29 : Certificate where
  inactiveUpper := 960739 / 1000000
  activeUpper := 11101 / 100000
  growthUpper := 17047975259552675936497588764672

def entry29 : Entry := ⟨cell29, certificate29⟩

def cell30 : Cell where
  lower := 1 / 128
  upper := 5 / 512
  thresholdUpper := 309375 / 307328
  modulusLower := 1503 / 500
  z := 17 / 5

def certificate30 : Certificate where
  inactiveUpper := 493659 / 500000
  activeUpper := 37111 / 1000000
  growthUpper := 12911458252644011931146448078303587251257344

def entry30 : Entry := ⟨cell30, certificate30⟩

def cell31 : Cell where
  lower := 7 / 512
  upper := 15 / 1024
  thresholdUpper := 311875 / 307328
  modulusLower := 3019 / 1000
  z := 53 / 20

def certificate31 : Certificate where
  inactiveUpper := 98271 / 100000
  activeUpper := 15463 / 200000
  growthUpper := 7475706103830454731143754704486400

def entry31 : Entry := ⟨cell31, certificate31⟩

def entries : List Entry := [entry28, entry29, entry30, entry31]

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

end ConstantDirectCover128Shard07
end SparseThresholdDominant
end CertifiedJL
