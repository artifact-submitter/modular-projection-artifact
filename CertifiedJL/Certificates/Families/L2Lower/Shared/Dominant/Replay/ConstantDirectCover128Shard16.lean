-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard16

open ConstantNumeric

def cell64 : Cell where
  lower := 5 / 128
  upper := 21 / 512
  thresholdUpper := 2500 / 2401
  modulusLower := 611 / 200
  z := 47 / 20

def certificate64 : Certificate where
  inactiveUpper := 478737 / 500000
  activeUpper := 29157 / 250000
  growthUpper := 6635368471505288969685169078272

def entry64 : Entry := ⟨cell64, certificate64⟩

def cell65 : Cell where
  lower := 5 / 128
  upper := 3 / 64
  thresholdUpper := 5625 / 5488
  modulusLower := 3013 / 1000
  z := 49 / 20

def certificate65 : Certificate where
  inactiveUpper := 238951 / 250000
  activeUpper := 27851 / 250000
  growthUpper := 42779467463469489459418831519744

def entry65 : Entry := ⟨cell65, certificate65⟩

def cell66 : Cell where
  lower := 9 / 256
  upper := 19 / 512
  thresholdUpper := 159375 / 153664
  modulusLower := 3049 / 1000
  z := 12 / 5

def certificate66 : Certificate where
  inactiveUpper := 960731 / 1000000
  activeUpper := 10961 / 100000
  growthUpper := 22626383036822706586564153049088

def entry66 : Entry := ⟨cell66, certificate66⟩

def cell67 : Cell where
  lower := 31 / 64
  upper := 1 / 2
  thresholdUpper := 625 / 1372
  modulusLower := 2
  z := 51 / 10

def certificate67 : Certificate where
  inactiveUpper := 305001 / 500000
  activeUpper := 95133 / 200000
  growthUpper := 183905852789689352198878658560

def entry67 : Entry := ⟨cell67, certificate67⟩

def entries : List Entry := [entry64, entry65, entry66, entry67]

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

end ConstantDirectCover128Shard16
end SparseThresholdDominant
end CertifiedJL
