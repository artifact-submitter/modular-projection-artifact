-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard27

open ConstantNumeric

def cell108 : Cell where
  lower := 0
  upper := 1 / 256
  thresholdUpper := 75625 / 76832
  modulusLower := 741 / 250
  z := 91 / 20

def certificate108 : Certificate where
  inactiveUpper := 1000323 / 1000000
  activeUpper := 5821 / 500000
  growthUpper := 256588482770207619227950253119228301307397916174458028032

def entry108 : Entry := ⟨cell108, certificate108⟩

def cell109 : Cell where
  lower := 13 / 512
  upper := 7 / 256
  thresholdUpper := 156875 / 153664
  modulusLower := 121 / 40
  z := 5 / 2

def certificate109 : Certificate where
  inactiveUpper := 485043 / 500000
  activeUpper := 11923 / 125000
  growthUpper := 140804869039443497612511211945984

def entry109 : Entry := ⟨cell109, certificate109⟩

def cell110 : Cell where
  lower := 1 / 128
  upper := 3 / 256
  thresholdUpper := 38125 / 38416
  modulusLower := 372 / 125
  z := 57 / 20

def certificate110 : Certificate where
  inactiveUpper := 989391 / 1000000
  activeUpper := 31609 / 500000
  growthUpper := 423507445065991158690736835376709632

def entry110 : Entry := ⟨cell110, certificate110⟩

def cell111 : Cell where
  lower := 11 / 256
  upper := 3 / 64
  thresholdUpper := 79375 / 76832
  modulusLower := 3037 / 1000
  z := 49 / 20

def certificate111 : Certificate where
  inactiveUpper := 475829 / 500000
  activeUpper := 55689 / 500000
  growthUpper := 76250488081966753253951889473536

def entry111 : Entry := ⟨cell111, certificate111⟩

def entries : List Entry := [entry108, entry109, entry110, entry111]

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

end ConstantDirectCover128Shard27
end SparseThresholdDominant
end CertifiedJL
