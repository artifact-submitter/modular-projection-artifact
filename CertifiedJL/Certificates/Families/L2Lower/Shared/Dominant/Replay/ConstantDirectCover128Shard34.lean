-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard34

open ConstantNumeric

def cell136 : Cell where
  lower := 31 / 64
  upper := 1 / 2
  thresholdUpper := 18125 / 38416
  modulusLower := 253 / 125
  z := 5

def certificate136 : Certificate where
  inactiveUpper := 611003 / 1000000
  activeUpper := 5793 / 12500
  growthUpper := 519259066901237455806374346752

def entry136 : Entry := ⟨cell136, certificate136⟩

def cell137 : Cell where
  lower := 1 / 128
  upper := 1 / 64
  thresholdUpper := 36875 / 38416
  modulusLower := 1457 / 500
  z := 3

def certificate137 : Certificate where
  inactiveUpper := 988843 / 1000000
  activeUpper := 2279 / 40000
  growthUpper := 1872010472340420781937282110210441216

def entry137 : Entry := ⟨cell137, certificate137⟩

def cell138 : Cell where
  lower := 1 / 16
  upper := 3 / 32
  thresholdUpper := 9375 / 9604
  modulusLower := 2863 / 1000
  z := 51 / 20

def certificate138 : Certificate where
  inactiveUpper := 929573 / 1000000
  activeUpper := 128699 / 1000000
  growthUpper := 22626383036822382327390982373376

def entry138 : Entry := ⟨cell138, certificate138⟩

def cell139 : Cell where
  lower := 5 / 16
  upper := 3 / 8
  thresholdUpper := 2500 / 2401
  modulusLower := 2863 / 1000
  z := 14 / 5

def certificate139 : Certificate where
  inactiveUpper := 742373 / 1000000
  activeUpper := 264097 / 1000000
  growthUpper := 5285630643895036511569810792059502592

def entry139 : Entry := ⟨cell139, certificate139⟩

def entries : List Entry := [entry136, entry137, entry138, entry139]

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

end ConstantDirectCover128Shard34
end SparseThresholdDominant
end CertifiedJL
