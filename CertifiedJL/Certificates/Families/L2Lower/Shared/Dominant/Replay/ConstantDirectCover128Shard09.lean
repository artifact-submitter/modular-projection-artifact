-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard09

open ConstantNumeric

def cell36 : Cell where
  lower := 1 / 64
  upper := 1 / 32
  thresholdUpper := 9375 / 9604
  modulusLower := 1457 / 500
  z := 51 / 20

def certificate36 : Certificate where
  inactiveUpper := 196213 / 200000
  activeUpper := 47313 / 500000
  growthUpper := 22626383036822382327390982373376

def entry36 : Entry := ⟨cell36, certificate36⟩

def cell37 : Cell where
  lower := 3 / 512
  upper := 7 / 1024
  thresholdUpper := 19375 / 19208
  modulusLower := 3009 / 1000
  z := 37 / 10

def certificate37 : Certificate where
  inactiveUpper := 30927 / 31250
  activeUpper := 423 / 15625
  growthUpper := 102157822516923126274845478770997280164481597440

def entry37 : Entry := ⟨cell37, certificate37⟩

def cell38 : Cell where
  lower := 1 / 256
  upper := 1 / 128
  thresholdUpper := 3125 / 3136
  modulusLower := 747 / 250
  z := 18 / 5

def certificate38 : Certificate where
  inactiveUpper := 993377 / 1000000
  activeUpper := 15117 / 500000
  growthUpper := 1533299832976233478925439683617758630079627264

def entry38 : Entry := ⟨cell38, certificate38⟩

def cell39 : Cell where
  lower := 1 / 64
  upper := 5 / 256
  thresholdUpper := 19375 / 19208
  modulusLower := 3
  z := 13 / 5

def certificate39 : Certificate where
  inactiveUpper := 19613 / 20000
  activeUpper := 41813 / 500000
  growthUpper := 1083495114492369041932284652945408

def entry39 : Entry := ⟨cell39, certificate39⟩

def entries : List Entry := [entry36, entry37, entry38, entry39]

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

end ConstantDirectCover128Shard09
end SparseThresholdDominant
end CertifiedJL
