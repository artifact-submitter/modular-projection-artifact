-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard01

open ConstantNumeric

def cell4 : Cell where
  lower := 5 / 512
  upper := 11 / 1024
  thresholdUpper := 155625 / 153664
  modulusLower := 377 / 125
  z := 13 / 4

def certificate4 : Certificate where
  inactiveUpper := 984841 / 1000000
  activeUpper := 43017 / 1000000
  growthUpper := 287698605257557643614917874928238974730240

def entry4 : Entry := ⟨cell4, certificate4⟩

def cell5 : Cell where
  lower := 7 / 512
  upper := 1 / 64
  thresholdUpper := 155625 / 153664
  modulusLower := 3013 / 1000
  z := 3

def certificate5 : Certificate where
  inactiveUpper := 49023 / 50000
  activeUpper := 1413 / 25000
  growthUpper := 186260648906889500046675548490864525312

def entry5 : Entry := ⟨cell5, certificate5⟩

def cell6 : Cell where
  lower := 7 / 256
  upper := 1 / 32
  thresholdUpper := 5625 / 5488
  modulusLower := 121 / 40
  z := 49 / 20

def certificate6 : Certificate where
  inactiveUpper := 968501 / 1000000
  activeUpper := 101993 / 1000000
  growthUpper := 42779467463469489459418831519744

def entry6 : Entry := ⟨cell6, certificate6⟩

def cell7 : Cell where
  lower := 15 / 1024
  upper := 1 / 64
  thresholdUpper := 78125 / 76832
  modulusLower := 1511 / 500
  z := 53 / 20

def certificate7 : Certificate where
  inactiveUpper := 981489 / 1000000
  activeUpper := 19443 / 250000
  growthUpper := 8740305844523062814803878320537600

def entry7 : Entry := ⟨cell7, certificate7⟩

def entries : List Entry := [entry4, entry5, entry6, entry7]

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

end ConstantDirectCover128Shard01
end SparseThresholdDominant
end CertifiedJL
