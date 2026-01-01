-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard33

open ConstantNumeric

def cell132 : Cell where
  lower := 0
  upper := 1 / 128
  thresholdUpper := 36875 / 38416
  modulusLower := 1457 / 500
  z := 33 / 10

def certificate132 : Certificate where
  inactiveUpper := 1000333 / 1000000
  activeUpper := 40281 / 1000000
  growthUpper := 7926965425027328544556226295428915658752

def entry132 : Entry := ⟨cell132, certificate132⟩

def cell133 : Cell where
  lower := 7 / 128
  upper := 1 / 16
  thresholdUpper := 5625 / 5488
  modulusLower := 3013 / 1000
  z := 5 / 2

def certificate133 : Certificate where
  inactiveUpper := 187701 / 200000
  activeUpper := 115433 / 1000000
  growthUpper := 189096111593227172226989513768960

def entry133 : Entry := ⟨cell133, certificate133⟩

def cell134 : Cell where
  lower := 1 / 32
  upper := 3 / 64
  thresholdUpper := 9375 / 9604
  modulusLower := 1457 / 500
  z := 51 / 20

def certificate134 : Certificate where
  inactiveUpper := 240719 / 250000
  activeUpper := 51477 / 500000
  growthUpper := 22626383036822382327390982373376

def entry134 : Entry := ⟨cell134, certificate134⟩

def cell135 : Cell where
  lower := 1 / 16
  upper := 1 / 8
  thresholdUpper := 625 / 686
  modulusLower := 2651 / 1000
  z := 27 / 10

def certificate135 : Certificate where
  inactiveUpper := 926351 / 1000000
  activeUpper := 68553 / 500000
  growthUpper := 9678056418181476329736919580672

def entry135 : Entry := ⟨cell135, certificate135⟩

def entries : List Entry := [entry132, entry133, entry134, entry135]

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

end ConstantDirectCover128Shard33
end SparseThresholdDominant
end CertifiedJL
