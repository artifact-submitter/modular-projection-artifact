-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard06

open ConstantNumeric

def cell24 : Cell where
  lower := 1 / 32
  upper := 9 / 256
  thresholdUpper := 158125 / 153664
  modulusLower := 3037 / 1000
  z := 12 / 5

def certificate24 : Certificate where
  inactiveUpper := 964901 / 1000000
  activeUpper := 108681 / 1000000
  growthUpper := 12844892618379718333584740712448

def entry24 : Entry := ⟨cell24, certificate24⟩

def cell25 : Cell where
  lower := 1 / 64
  upper := 9 / 512
  thresholdUpper := 311875 / 307328
  modulusLower := 3019 / 1000
  z := 13 / 5

def certificate25 : Certificate where
  inactiveUpper := 980643 / 1000000
  activeUpper := 3299 / 40000
  growthUpper := 1716359432877547777120145346920448

def entry25 : Entry := ⟨cell25, certificate25⟩

def cell26 : Cell where
  lower := 17 / 1024
  upper := 9 / 512
  thresholdUpper := 313125 / 307328
  modulusLower := 121 / 40
  z := 13 / 5

def certificate26 : Certificate where
  inactiveUpper := 979449 / 1000000
  activeUpper := 82379 / 1000000
  growthUpper := 2332360961548867473549147909390336

def entry26 : Entry := ⟨cell26, certificate26⟩

def cell27 : Cell where
  lower := 1 / 256
  upper := 3 / 512
  thresholdUpper := 154375 / 153664
  modulusLower := 3
  z := 19 / 5

def certificate27 : Certificate where
  inactiveUpper := 248247 / 250000
  activeUpper := 24373 / 1000000
  growthUpper := 1216233612295473759780438137927082441375999852544

def entry27 : Entry := ⟨cell27, certificate27⟩

def entries : List Entry := [entry24, entry25, entry26, entry27]

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

end ConstantDirectCover128Shard06
end SparseThresholdDominant
end CertifiedJL
