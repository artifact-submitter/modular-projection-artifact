-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard08

open ConstantNumeric

def cell32 : Cell where
  lower := 3 / 128
  upper := 13 / 512
  thresholdUpper := 5625 / 5488
  modulusLower := 3031 / 1000
  z := 5 / 2

def certificate32 : Certificate where
  inactiveUpper := 121539 / 125000
  activeUpper := 94339 / 1000000
  growthUpper := 189096111593227172226989513768960

def entry32 : Entry := ⟨cell32, certificate32⟩

def cell33 : Cell where
  lower := 9 / 1024
  upper := 5 / 512
  thresholdUpper := 44375 / 43904
  modulusLower := 3013 / 1000
  z := 17 / 5

def certificate33 : Certificate where
  inactiveUpper := 492863 / 500000
  activeUpper := 579 / 15625
  growthUpper := 19281623304981718125544743385893717149745152

def entry33 : Entry := ⟨cell33, certificate33⟩

def cell34 : Cell where
  lower := 3 / 256
  upper := 13 / 1024
  thresholdUpper := 155625 / 153664
  modulusLower := 377 / 125
  z := 16 / 5

def certificate34 : Certificate where
  inactiveUpper := 982111 / 1000000
  activeUpper := 45861 / 1000000
  growthUpper := 66248252589342385247083378637499044724736

def entry34 : Entry := ⟨cell34, certificate34⟩

def cell35 : Cell where
  lower := 1 / 16
  upper := 3 / 32
  thresholdUpper := 19375 / 19208
  modulusLower := 741 / 250
  z := 49 / 20

def certificate35 : Certificate where
  inactiveUpper := 18641 / 20000
  activeUpper := 137031 / 1000000
  growthUpper := 13465449827449640848579262152704

def entry35 : Entry := ⟨cell35, certificate35⟩

def entries : List Entry := [entry32, entry33, entry34, entry35]

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

end ConstantDirectCover128Shard08
end SparseThresholdDominant
end CertifiedJL
