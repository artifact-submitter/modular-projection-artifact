-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard13

open ConstantNumeric

def cell52 : Cell where
  lower := 1 / 128
  upper := 9 / 1024
  thresholdUpper := 19375 / 19208
  modulusLower := 3009 / 1000
  z := 7 / 2

def certificate52 : Certificate where
  inactiveUpper := 49347 / 50000
  activeUpper := 522 / 15625
  growthUpper := 294078656474174210027035423497219323738456064

def entry52 : Entry := ⟨cell52, certificate52⟩

def cell53 : Cell where
  lower := 21 / 1024
  upper := 11 / 512
  thresholdUpper := 314375 / 307328
  modulusLower := 3031 / 1000
  z := 51 / 20

def certificate53 : Certificate where
  inactiveUpper := 243801 / 250000
  activeUpper := 11021 / 125000
  growthUpper := 719145406848703603712076667682816

def entry53 : Entry := ⟨cell53, certificate53⟩

def cell54 : Cell where
  lower := 1 / 256
  upper := 5 / 1024
  thresholdUpper := 309375 / 307328
  modulusLower := 1503 / 500
  z := 4

def certificate54 : Certificate where
  inactiveUpper := 496301 / 500000
  activeUpper := 3971 / 200000
  growthUpper := 522434525299984629622418686066001232485511180845056

def entry54 : Entry := ⟨cell54, certificate54⟩

def cell55 : Cell where
  lower := 1 / 128
  upper := 5 / 512
  thresholdUpper := 154375 / 153664
  modulusLower := 3
  z := 69 / 20

def certificate55 : Certificate where
  inactiveUpper := 987131 / 1000000
  activeUpper := 17711 / 500000
  growthUpper := 45345258075298595204711651301976951597563904

def entry55 : Entry := ⟨cell55, certificate55⟩

def entries : List Entry := [entry52, entry53, entry54, entry55]

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

end ConstantDirectCover128Shard13
end SparseThresholdDominant
end CertifiedJL
