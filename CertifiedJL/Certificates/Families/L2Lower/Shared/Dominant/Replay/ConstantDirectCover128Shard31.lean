-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard31

open ConstantNumeric

def cell124 : Cell where
  lower := 5 / 256
  upper := 3 / 128
  thresholdUpper := 76875 / 76832
  modulusLower := 747 / 250
  z := 13 / 5

def certificate124 : Certificate where
  inactiveUpper := 243979 / 250000
  activeUpper := 21401 / 250000
  growthUpper := 586748397822272799053678425145344

def entry124 : Entry := ⟨cell124, certificate124⟩

def cell125 : Cell where
  lower := 3 / 8
  upper := 7 / 16
  thresholdUpper := 1250 / 2401
  modulusLower := 253 / 125
  z := 99 / 20

def certificate125 : Certificate where
  inactiveUpper := 647583 / 1000000
  activeUpper := 403619 / 1000000
  growthUpper := 289131953964106141554739247054848

def entry125 : Entry := ⟨cell125, certificate125⟩

def cell126 : Cell where
  lower := 3 / 128
  upper := 1 / 32
  thresholdUpper := 38125 / 38416
  modulusLower := 741 / 250
  z := 51 / 20

def certificate126 : Certificate where
  inactiveUpper := 485901 / 500000
  activeUpper := 18821 / 200000
  growthUpper := 75356380601786489165928783151104

def entry126 : Entry := ⟨cell126, certificate126⟩

def cell127 : Cell where
  lower := 3 / 16
  upper := 1 / 4
  thresholdUpper := 2500 / 2401
  modulusLower := 2863 / 1000
  z := 11 / 4

def certificate127 : Certificate where
  inactiveUpper := 163433 / 200000
  activeUpper := 199699 / 1000000
  growthUpper := 1167896597361686657383568057770704896

def entry127 : Entry := ⟨cell127, certificate127⟩

def entries : List Entry := [entry124, entry125, entry126, entry127]

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

end ConstantDirectCover128Shard31
end SparseThresholdDominant
end CertifiedJL
