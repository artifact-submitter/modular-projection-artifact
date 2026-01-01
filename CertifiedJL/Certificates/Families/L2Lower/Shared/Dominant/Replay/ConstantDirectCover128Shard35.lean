-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard35

open ConstantNumeric

def cell140 : Cell where
  lower := 1 / 64
  upper := 1 / 32
  thresholdUpper := 18125 / 19208
  modulusLower := 2863 / 1000
  z := 11 / 4

def certificate140 : Certificate where
  inactiveUpper := 489803 / 500000
  activeUpper := 79823 / 1000000
  growthUpper := 485836746815602898314677576531968

def entry140 : Entry := ⟨cell140, certificate140⟩

def cell141 : Cell where
  lower := 15 / 32
  upper := 31 / 64
  thresholdUpper := 9375 / 19208
  modulusLower := 253 / 125
  z := 5

def certificate141 : Certificate where
  inactiveUpper := 613243 / 1000000
  activeUpper := 448231 / 1000000
  growthUpper := 5494187703083281691249087610880

def entry141 : Entry := ⟨cell141, certificate141⟩

def cell142 : Cell where
  lower := 1 / 4
  upper := 5 / 16
  thresholdUpper := 2500 / 2401
  modulusLower := 2863 / 1000
  z := 14 / 5

def certificate142 : Certificate where
  inactiveUpper := 387557 / 500000
  activeUpper := 115217 / 500000
  growthUpper := 5285630643895036511569810792059502592

def entry142 : Entry := ⟨cell142, certificate142⟩

def cell143 : Cell where
  lower := 0
  upper := 1 / 16
  thresholdUpper := 1875 / 2401
  modulusLower := 121 / 50
  z := 31 / 10

def certificate143 : Certificate where
  inactiveUpper := 500357 / 500000
  activeUpper := 20007 / 250000
  growthUpper := 3119024855032204963651291971584

def entry143 : Entry := ⟨cell143, certificate143⟩

def entries : List Entry := [entry140, entry141, entry142, entry143]

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

end ConstantDirectCover128Shard35
end SparseThresholdDominant
end CertifiedJL
