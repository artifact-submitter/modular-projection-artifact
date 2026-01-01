-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard17

open ConstantNumeric

def cell68 : Cell where
  lower := 1 / 64
  upper := 9 / 512
  thresholdUpper := 155625 / 153664
  modulusLower := 3013 / 1000
  z := 53 / 20

def certificate68 : Certificate where
  inactiveUpper := 245069 / 250000
  activeUpper := 78797 / 1000000
  growthUpper := 6394076219411460369306588461137920

def entry68 : Entry := ⟨cell68, certificate68⟩

def cell69 : Cell where
  lower := 17 / 1024
  upper := 9 / 512
  thresholdUpper := 78125 / 76832
  modulusLower := 1511 / 500
  z := 53 / 20

def certificate69 : Certificate where
  inactiveUpper := 979061 / 1000000
  activeUpper := 78703 / 1000000
  growthUpper := 8740305844523062814803878320537600

def entry69 : Entry := ⟨cell69, certificate69⟩

def cell70 : Cell where
  lower := 25 / 1024
  upper := 13 / 512
  thresholdUpper := 315625 / 307328
  modulusLower := 3037 / 1000
  z := 5 / 2

def certificate70 : Certificate where
  inactiveUpper := 971193 / 1000000
  activeUpper := 18847 / 200000
  growthUpper := 219136671719195004217530049888256

def entry70 : Entry := ⟨cell70, certificate70⟩

def cell71 : Cell where
  lower := 5 / 512
  upper := 3 / 256
  thresholdUpper := 154375 / 153664
  modulusLower := 3
  z := 14 / 5

def certificate71 : Certificate where
  inactiveUpper := 493471 / 500000
  activeUpper := 33037 / 500000
  growthUpper := 270521858679600946340030215008288768

def entry71 : Entry := ⟨cell71, certificate71⟩

def entries : List Entry := [entry68, entry69, entry70, entry71]

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

end ConstantDirectCover128Shard17
end SparseThresholdDominant
end CertifiedJL
