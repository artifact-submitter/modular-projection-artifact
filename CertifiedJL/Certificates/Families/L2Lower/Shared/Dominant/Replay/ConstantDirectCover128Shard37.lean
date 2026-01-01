-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard37

open ConstantNumeric

def cell148 : Cell where
  lower := 15 / 32
  upper := 31 / 64
  thresholdUpper := 625 / 1372
  modulusLower := 2
  z := 26 / 5

def certificate148 : Certificate where
  inactiveUpper := 19071 / 31250
  activeUpper := 456483 / 1000000
  growthUpper := 689170084081820343983377743872

def entry148 : Entry := ⟨cell148, certificate148⟩

def cell149 : Cell where
  lower := 15 / 32
  upper := 1 / 2
  thresholdUpper := 8125 / 19208
  modulusLower := 2
  z := 21 / 4

def certificate149 : Certificate where
  inactiveUpper := 7681 / 12500
  activeUpper := 94031 / 200000
  growthUpper := 9412415749516474731173249024

def entry149 : Entry := ⟨cell149, certificate149⟩

def cell150 : Cell where
  lower := 7 / 16
  upper := 1 / 2
  thresholdUpper := 625 / 686
  modulusLower := 2651 / 1000
  z := 31 / 10

def certificate150 : Certificate where
  inactiveUpper := 339609 / 500000
  activeUpper := 10409 / 31250
  growthUpper := 376387402375058447348657269101297664

def entry150 : Entry := ⟨cell150, certificate150⟩

def cell151 : Cell where
  lower := 1 / 32
  upper := 1 / 16
  thresholdUpper := 625 / 686
  modulusLower := 2759 / 1000
  z := 27 / 10

def certificate151 : Certificate where
  inactiveUpper := 960921 / 1000000
  activeUpper := 12529 / 125000
  growthUpper := 9678056418181476329736919580672

def entry151 : Entry := ⟨cell151, certificate151⟩

def entries : List Entry := [entry148, entry149, entry150, entry151]

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

end ConstantDirectCover128Shard37
end SparseThresholdDominant
end CertifiedJL
