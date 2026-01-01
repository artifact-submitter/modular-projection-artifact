-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard36

open ConstantNumeric

def cell144 : Cell where
  lower := 3 / 8
  upper := 7 / 16
  thresholdUpper := 3125 / 4802
  modulusLower := 541 / 250
  z := 87 / 20

def certificate144 : Certificate where
  inactiveUpper := 329819 / 500000
  activeUpper := 355007 / 1000000
  growthUpper := 454565667894754994725778152482668544

def entry144 : Entry := ⟨cell144, certificate144⟩

def cell145 : Cell where
  lower := 1 / 8
  upper := 5 / 32
  thresholdUpper := 2500 / 2401
  modulusLower := 741 / 250
  z := 13 / 5

def certificate145 : Certificate where
  inactiveUpper := 870501 / 1000000
  activeUpper := 39603 / 250000
  growthUpper := 12598740697234927720272354468691968

def entry145 : Entry := ⟨cell145, certificate145⟩

def cell146 : Cell where
  lower := 1 / 8
  upper := 3 / 16
  thresholdUpper := 9375 / 9604
  modulusLower := 2863 / 1000
  z := 27 / 10

def certificate146 : Certificate where
  inactiveUpper := 54209 / 62500
  activeUpper := 6749 / 40000
  growthUpper := 1580338287453429054013752408539136

def entry146 : Entry := ⟨cell146, certificate146⟩

def cell147 : Cell where
  lower := 3 / 64
  upper := 1 / 16
  thresholdUpper := 9375 / 9604
  modulusLower := 1457 / 500
  z := 13 / 5

def certificate147 : Certificate where
  inactiveUpper := 94471 / 100000
  activeUpper := 53651 / 500000
  growthUpper := 93180873496862003008730325581824

def entry147 : Entry := ⟨cell147, certificate147⟩

def entries : List Entry := [entry144, entry145, entry146, entry147]

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

end ConstantDirectCover128Shard36
end SparseThresholdDominant
end CertifiedJL
