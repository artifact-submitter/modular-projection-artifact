-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard04

open ConstantNumeric

def cell16 : Cell where
  lower := 1 / 128
  upper := 3 / 256
  thresholdUpper := 76875 / 76832
  modulusLower := 747 / 250
  z := 13 / 4

def certificate16 : Certificate where
  inactiveUpper := 987889 / 1000000
  activeUpper := 5449 / 125000
  growthUpper := 91092903922801497124896907299705103319040

def entry16 : Entry := ⟨cell16, certificate16⟩

def cell17 : Cell where
  lower := 11 / 512
  upper := 3 / 128
  thresholdUpper := 314375 / 307328
  modulusLower := 3031 / 1000
  z := 5 / 2

def certificate17 : Certificate where
  inactiveUpper := 194911 / 200000
  activeUpper := 93319 / 1000000
  growthUpper := 163173690369349519309320853913600

def entry17 : Entry := ⟨cell17, certificate17⟩

def cell18 : Cell where
  lower := 17 / 512
  upper := 9 / 256
  thresholdUpper := 159375 / 153664
  modulusLower := 3049 / 1000
  z := 12 / 5

def certificate18 : Certificate where
  inactiveUpper := 192561 / 200000
  activeUpper := 54229 / 500000
  growthUpper := 22626383036822706586564153049088

def entry18 : Entry := ⟨cell18, certificate18⟩

def cell19 : Cell where
  lower := 1 / 128
  upper := 9 / 1024
  thresholdUpper := 44375 / 43904
  modulusLower := 3013 / 1000
  z := 69 / 20

def certificate19 : Certificate where
  inactiveUpper := 987127 / 1000000
  activeUpper := 35011 / 1000000
  growthUpper := 83488426061062525465450669214217212660809728

def entry19 : Entry := ⟨cell19, certificate19⟩

def entries : List Entry := [entry16, entry17, entry18, entry19]

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

end ConstantDirectCover128Shard04
end SparseThresholdDominant
end CertifiedJL
