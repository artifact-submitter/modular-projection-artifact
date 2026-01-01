-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard14

open ConstantNumeric

def cell56 : Cell where
  lower := 9 / 512
  upper := 19 / 1024
  thresholdUpper := 313125 / 307328
  modulusLower := 121 / 40
  z := 13 / 5

def certificate56 : Certificate where
  inactiveUpper := 978263 / 1000000
  activeUpper := 82853 / 1000000
  growthUpper := 2332360961548867473549147909390336

def entry56 : Entry := ⟨cell56, certificate56⟩

def cell57 : Cell where
  lower := 9 / 1024
  upper := 5 / 512
  thresholdUpper := 19375 / 19208
  modulusLower := 3009 / 1000
  z := 17 / 5

def certificate57 : Certificate where
  inactiveUpper := 492863 / 500000
  activeUpper := 579 / 15625
  growthUpper := 15778272223075608332783751992184558923546624

def entry57 : Entry := ⟨cell57, certificate57⟩

def cell58 : Cell where
  lower := 1 / 32
  upper := 17 / 512
  thresholdUpper := 79375 / 76832
  modulusLower := 3043 / 1000
  z := 12 / 5

def certificate58 : Certificate where
  inactiveUpper := 964893 / 1000000
  activeUpper := 21467 / 200000
  growthUpper := 17047975259552675936497588764672

def entry58 : Entry := ⟨cell58, certificate58⟩

def cell59 : Cell where
  lower := 5 / 1024
  upper := 3 / 512
  thresholdUpper := 309375 / 307328
  modulusLower := 1503 / 500
  z := 77 / 20

def certificate59 : Certificate where
  inactiveUpper := 991059 / 1000000
  activeUpper := 23203 / 1000000
  growthUpper := 6550398569594759788441357498284810868002970927104

def entry59 : Entry := ⟨cell59, certificate59⟩

def entries : List Entry := [entry56, entry57, entry58, entry59]

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

end ConstantDirectCover128Shard14
end SparseThresholdDominant
end CertifiedJL
