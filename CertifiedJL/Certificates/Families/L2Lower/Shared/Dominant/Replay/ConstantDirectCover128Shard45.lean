-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard45

open ConstantNumeric

def cell180 : Cell where
  lower := 3 / 8
  upper := 7 / 16
  thresholdUpper := 1875 / 4802
  modulusLower := 2
  z := 29 / 5

def certificate180 : Certificate where
  inactiveUpper := 79151 / 125000
  activeUpper := 194163 / 500000
  growthUpper := 33646630588316904451754426368

def entry180 : Entry := ⟨cell180, certificate180⟩

def cell181 : Cell where
  lower := 1 / 4
  upper := 3 / 8
  thresholdUpper := 1875 / 4802
  modulusLower := 2
  z := 119 / 20

def certificate181 : Certificate where
  inactiveUpper := 139061 / 200000
  activeUpper := 317393 / 1000000
  growthUpper := 183905852789691991026785320960

def entry181 : Entry := ⟨cell181, certificate181⟩

def cell182 : Cell where
  lower := 1 / 4
  upper := 5 / 16
  thresholdUpper := 1250 / 2401
  modulusLower := 2
  z := 28 / 5

def certificate182 : Certificate where
  inactiveUpper := 136389 / 200000
  activeUpper := 52241 / 200000
  growthUpper := 5285630643895036511569810792059502592

def entry182 : Entry := ⟨cell182, certificate182⟩

def cell183 : Cell where
  lower := 3 / 8
  upper := 1 / 2
  thresholdUpper := 625 / 2401
  modulusLower := 2
  z := 129 / 20

def certificate183 : Certificate where
  inactiveUpper := 650201 / 1000000
  activeUpper := 434737 / 1000000
  growthUpper := 1413845231724223528960

def entry183 : Entry := ⟨cell183, certificate183⟩

def entries : List Entry := [entry180, entry181, entry182, entry183]

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

end ConstantDirectCover128Shard45
end SparseThresholdDominant
end CertifiedJL
