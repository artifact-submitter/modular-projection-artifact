-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard43

open ConstantNumeric

def cell172 : Cell where
  lower := 0
  upper := 1 / 16
  thresholdUpper := 3125 / 4802
  modulusLower := 541 / 250
  z := 23 / 5

def certificate172 : Certificate where
  inactiveUpper := 500569 / 500000
  activeUpper := 18089 / 500000
  growthUpper := 50890350200341766267502006549652439040

def entry172 : Entry := ⟨cell172, certificate172⟩

def cell173 : Cell where
  lower := 7 / 16
  upper := 15 / 32
  thresholdUpper := 1250 / 2401
  modulusLower := 419 / 200
  z := 49 / 10

def certificate173 : Certificate where
  inactiveUpper := 31183 / 50000
  activeUpper := 394711 / 1000000
  growthUpper := 135909521026720658266858721378304

def entry173 : Entry := ⟨cell173, certificate173⟩

def cell174 : Cell where
  lower := 3 / 8
  upper := 7 / 16
  thresholdUpper := 1875 / 2401
  modulusLower := 121 / 50
  z := 37 / 10

def certificate174 : Certificate where
  inactiveUpper := 677769 / 1000000
  activeUpper := 60309 / 200000
  growthUpper := 2484566369392405912902181554529239040

def entry174 : Entry := ⟨cell174, certificate174⟩

def cell175 : Cell where
  lower := 1 / 16
  upper := 1 / 8
  thresholdUpper := 1875 / 2401
  modulusLower := 121 / 50
  z := 67 / 20

def certificate175 : Certificate where
  inactiveUpper := 45563 / 50000
  activeUpper := 5153 / 50000
  growthUpper := 897150709860186691629267051085824

def entry175 : Entry := ⟨cell175, certificate175⟩

def entries : List Entry := [entry172, entry173, entry174, entry175]

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

end ConstantDirectCover128Shard43
end SparseThresholdDominant
end CertifiedJL
