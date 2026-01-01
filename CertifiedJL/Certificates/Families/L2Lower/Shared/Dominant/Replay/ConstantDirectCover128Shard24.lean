-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard24

open ConstantNumeric

def cell96 : Cell where
  lower := 3 / 64
  upper := 7 / 128
  thresholdUpper := 79375 / 76832
  modulusLower := 3037 / 1000
  z := 49 / 20

def certificate96 : Certificate where
  inactiveUpper := 947609 / 1000000
  activeUpper := 115593 / 1000000
  growthUpper := 76250488081966753253951889473536

def entry96 : Entry := ⟨cell96, certificate96⟩

def cell97 : Cell where
  lower := 7 / 16
  upper := 1 / 2
  thresholdUpper := 2500 / 2401
  modulusLower := 741 / 250
  z := 53 / 20

def certificate97 : Certificate where
  inactiveUpper := 350157 / 500000
  activeUpper := 332409 / 1000000
  growthUpper := 57018994707430806776593378147565568

def entry97 : Entry := ⟨cell97, certificate97⟩

def cell98 : Cell where
  lower := 3 / 128
  upper := 13 / 512
  thresholdUpper := 156875 / 153664
  modulusLower := 121 / 40
  z := 5 / 2

def certificate98 : Certificate where
  inactiveUpper := 121539 / 125000
  activeUpper := 47171 / 500000
  growthUpper := 140804869039443497612511211945984

def entry98 : Entry := ⟨cell98, certificate98⟩

def cell99 : Cell where
  lower := 3 / 64
  upper := 13 / 256
  thresholdUpper := 2500 / 2401
  modulusLower := 3049 / 1000
  z := 49 / 20

def certificate99 : Certificate where
  inactiveUpper := 473793 / 500000
  activeUpper := 113471 / 1000000
  growthUpper := 135909521026720658266858721378304

def entry99 : Entry := ⟨cell99, certificate99⟩

def entries : List Entry := [entry96, entry97, entry98, entry99]

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

end ConstantDirectCover128Shard24
end SparseThresholdDominant
end CertifiedJL
