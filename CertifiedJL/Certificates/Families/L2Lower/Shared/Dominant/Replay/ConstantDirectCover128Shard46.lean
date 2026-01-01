-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard46

open ConstantNumeric

def cell184 : Cell where
  lower := 1 / 16
  upper := 1 / 8
  thresholdUpper := 1250 / 2401
  modulusLower := 2
  z := 28 / 5

def certificate184 : Certificate where
  inactiveUpper := 866049 / 1000000
  activeUpper := 37201 / 500000
  growthUpper := 5285630643895036511569810792059502592

def entry184 : Entry := ⟨cell184, certificate184⟩

def cell185 : Cell where
  lower := 0
  upper := 1 / 8
  thresholdUpper := 625 / 2401
  modulusLower := 2
  z := 7

def certificate185 : Certificate where
  inactiveUpper := 126319 / 125000
  activeUpper := 24013 / 500000
  growthUpper := 89857849855989369536512

def entry185 : Entry := ⟨cell185, certificate185⟩

def cell186 : Cell where
  lower := 1 / 4
  upper := 3 / 8
  thresholdUpper := 625 / 2401
  modulusLower := 2
  z := 29 / 4

def certificate186 : Certificate where
  inactiveUpper := 136251 / 200000
  activeUpper := 71217 / 250000
  growthUpper := 593159575398410266607616

def entry186 : Entry := ⟨cell186, certificate186⟩

def cell187 : Cell where
  lower := 1 / 8
  upper := 1 / 4
  thresholdUpper := 625 / 2401
  modulusLower := 2
  z := 31 / 4

def certificate187 : Certificate where
  inactiveUpper := 76247 / 100000
  activeUpper := 71583 / 500000
  growthUpper := 25846550614928639530106880

def entry187 : Entry := ⟨cell187, certificate187⟩

def entries : List Entry := [entry184, entry185, entry186, entry187]

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

end ConstantDirectCover128Shard46
end SparseThresholdDominant
end CertifiedJL
