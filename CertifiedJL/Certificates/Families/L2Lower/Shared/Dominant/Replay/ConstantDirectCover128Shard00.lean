-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard00

open ConstantNumeric

def cell0 : Cell where
  lower := 5 / 256
  upper := 11 / 512
  thresholdUpper := 156875 / 153664
  modulusLower := 121 / 40
  z := 51 / 20

def certificate0 : Certificate where
  inactiveUpper := 24409 / 25000
  activeUpper := 22067 / 250000
  growthUpper := 618733454942712423755006649303040

def entry0 : Entry := ⟨cell0, certificate0⟩

def cell1 : Cell where
  lower := 3 / 512
  upper := 1 / 128
  thresholdUpper := 309375 / 307328
  modulusLower := 1503 / 500
  z := 7 / 2

def certificate1 : Certificate where
  inactiveUpper := 198047 / 200000
  activeUpper := 33113 / 1000000
  growthUpper := 239231331664563921414970742190928920771035136

def entry1 : Entry := ⟨cell1, certificate1⟩

def cell2 : Cell where
  lower := 15 / 512
  upper := 1 / 32
  thresholdUpper := 79375 / 76832
  modulusLower := 3043 / 1000
  z := 49 / 20

def certificate2 : Certificate where
  inactiveUpper := 966337 / 1000000
  activeUpper := 50887 / 500000
  growthUpper := 76250488081966753253951889473536

def entry2 : Entry := ⟨cell2, certificate2⟩

def cell3 : Cell where
  lower := 3 / 256
  upper := 1 / 64
  thresholdUpper := 154375 / 153664
  modulusLower := 3
  z := 3

def certificate3 : Certificate where
  inactiveUpper := 983231 / 1000000
  activeUpper := 56667 / 1000000
  growthUpper := 91783642810021835564426570788746821632

def entry3 : Entry := ⟨cell3, certificate3⟩

def entries : List Entry := [entry0, entry1, entry2, entry3]

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

end ConstantDirectCover128Shard00
end SparseThresholdDominant
end CertifiedJL
