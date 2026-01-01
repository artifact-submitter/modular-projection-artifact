-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard41

open ConstantNumeric

def cell164 : Cell where
  lower := 1 / 8
  upper := 1 / 4
  thresholdUpper := 3125 / 4802
  modulusLower := 541 / 250
  z := 43 / 10

def certificate164 : Certificate where
  inactiveUpper := 410333 / 500000
  activeUpper := 186439 / 1000000
  growthUpper := 176924863806768424492373388197625856

def entry164 : Entry := ⟨cell164, certificate164⟩

def cell165 : Cell where
  lower := 3 / 8
  upper := 7 / 16
  thresholdUpper := 625 / 1372
  modulusLower := 2
  z := 107 / 20

def certificate165 : Certificate where
  inactiveUpper := 64037 / 100000
  activeUpper := 403391 / 1000000
  growthUpper := 4999455607029321978561328840704

def entry165 : Entry := ⟨cell165, certificate165⟩

def cell166 : Cell where
  lower := 1 / 8
  upper := 3 / 16
  thresholdUpper := 625 / 686
  modulusLower := 2651 / 1000
  z := 3

def certificate166 : Certificate where
  inactiveUpper := 856087 / 1000000
  activeUpper := 76071 / 500000
  growthUpper := 26802379169318557748975668589232128

def entry166 : Entry := ⟨cell166, certificate166⟩

def cell167 : Cell where
  lower := 3 / 8
  upper := 7 / 16
  thresholdUpper := 625 / 686
  modulusLower := 2651 / 1000
  z := 16 / 5

def certificate167 : Certificate where
  inactiveUpper := 174161 / 250000
  activeUpper := 290197 / 1000000
  growthUpper := 5285630643895111479137726347677270016

def entry167 : Entry := ⟨cell167, certificate167⟩

def entries : List Entry := [entry164, entry165, entry166, entry167]

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

end ConstantDirectCover128Shard41
end SparseThresholdDominant
end CertifiedJL
