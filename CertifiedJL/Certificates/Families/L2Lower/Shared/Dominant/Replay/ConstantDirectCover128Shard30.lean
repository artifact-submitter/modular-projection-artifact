-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard30

open ConstantNumeric

def cell120 : Cell where
  lower := 1 / 128
  upper := 1 / 64
  thresholdUpper := 9375 / 9604
  modulusLower := 2939 / 1000
  z := 14 / 5

def certificate120 : Certificate where
  inactiveUpper := 494797 / 500000
  activeUpper := 1709 / 25000
  growthUpper := 26802379169318174979036139116036096

def entry120 : Entry := ⟨cell120, certificate120⟩

def cell121 : Cell where
  lower := 3 / 256
  upper := 1 / 64
  thresholdUpper := 38125 / 38416
  modulusLower := 372 / 125
  z := 14 / 5

def certificate121 : Certificate where
  inactiveUpper := 984341 / 1000000
  activeUpper := 13603 / 200000
  growthUpper := 100439423898243485854452492076580864

def entry121 : Entry := ⟨cell121, certificate121⟩

def cell122 : Cell where
  lower := 3 / 8
  upper := 7 / 16
  thresholdUpper := 2500 / 2401
  modulusLower := 2863 / 1000
  z := 11 / 4

def certificate122 : Certificate where
  inactiveUpper := 358913 / 500000
  activeUpper := 300351 / 1000000
  growthUpper := 1167896597361686657383568057770704896

def entry122 : Entry := ⟨cell122, certificate122⟩

def cell123 : Cell where
  lower := 0
  upper := 1 / 64
  thresholdUpper := 18125 / 19208
  modulusLower := 2863 / 1000
  z := 57 / 20

def certificate123 : Certificate where
  inactiveUpper := 500179 / 500000
  activeUpper := 13119 / 200000
  growthUpper := 7497783029288037013870533624725504

def entry123 : Entry := ⟨cell123, certificate123⟩

def entries : List Entry := [entry120, entry121, entry122, entry123]

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

end ConstantDirectCover128Shard30
end SparseThresholdDominant
end CertifiedJL
