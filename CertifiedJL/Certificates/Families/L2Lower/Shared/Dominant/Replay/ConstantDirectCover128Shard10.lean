-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard10

open ConstantNumeric

def cell40 : Cell where
  lower := 1 / 32
  upper := 5 / 128
  thresholdUpper := 78125 / 76832
  modulusLower := 3013 / 1000
  z := 12 / 5

def certificate40 : Certificate where
  inactiveUpper := 964919 / 1000000
  activeUpper := 5573 / 50000
  growthUpper := 5494187703083205130055422312448

def entry40 : Entry := ⟨cell40, certificate40⟩

def cell41 : Cell where
  lower := 13 / 512
  upper := 7 / 256
  thresholdUpper := 315625 / 307328
  modulusLower := 3037 / 1000
  z := 49 / 20

def certificate41 : Certificate where
  inactiveUpper := 970663 / 1000000
  activeUpper := 9963 / 100000
  growthUpper := 49429610409340651326655126568960

def entry41 : Entry := ⟨cell41, certificate41⟩

def cell42 : Cell where
  lower := 9 / 512
  upper := 5 / 256
  thresholdUpper := 78125 / 76832
  modulusLower := 3019 / 1000
  z := 13 / 5

def certificate42 : Certificate where
  inactiveUpper := 978267 / 1000000
  activeUpper := 83429 / 1000000
  growthUpper := 2000792277381574264456810439114752

def entry42 : Entry := ⟨cell42, certificate42⟩

def cell43 : Cell where
  lower := 5 / 512
  upper := 11 / 1024
  thresholdUpper := 44375 / 43904
  modulusLower := 3013 / 1000
  z := 33 / 10

def certificate43 : Certificate where
  inactiveUpper := 984609 / 1000000
  activeUpper := 41063 / 1000000
  growthUpper := 1028438282953271172208770935166867234357248

def entry43 : Entry := ⟨cell43, certificate43⟩

def entries : List Entry := [entry40, entry41, entry42, entry43]

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

end ConstantDirectCover128Shard10
end SparseThresholdDominant
end CertifiedJL
