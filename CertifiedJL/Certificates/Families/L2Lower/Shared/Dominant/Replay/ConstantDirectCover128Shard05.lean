-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard05

open ConstantNumeric

def cell20 : Cell where
  lower := 5 / 512
  upper := 3 / 256
  thresholdUpper := 19375 / 19208
  modulusLower := 1503 / 500
  z := 16 / 5

def certificate20 : Certificate where
  inactiveUpper := 492539 / 500000
  activeUpper := 22763 / 500000
  growthUpper := 45420438518815651948935681588437937291264

def entry20 : Entry := ⟨cell20, certificate20⟩

def cell21 : Cell where
  lower := 11 / 1024
  upper := 3 / 256
  thresholdUpper := 155625 / 153664
  modulusLower := 377 / 125
  z := 16 / 5

def certificate21 : Certificate where
  inactiveUpper := 983589 / 1000000
  activeUpper := 22731 / 500000
  growthUpper := 66248252589342385247083378637499044724736

def entry21 : Entry := ⟨cell21, certificate21⟩

def cell22 : Cell where
  lower := 1 / 16
  upper := 5 / 64
  thresholdUpper := 2500 / 2401
  modulusLower := 3013 / 1000
  z := 12 / 5

def certificate22 : Certificate where
  inactiveUpper := 233291 / 250000
  activeUpper := 66497 / 500000
  growthUpper := 30030147365573506575491655532544

def entry22 : Entry := ⟨cell22, certificate22⟩

def cell23 : Cell where
  lower := 19 / 512
  upper := 5 / 128
  thresholdUpper := 2500 / 2401
  modulusLower := 611 / 200
  z := 47 / 20

def certificate23 : Certificate where
  inactiveUpper := 239871 / 250000
  activeUpper := 14429 / 125000
  growthUpper := 6635368471505288969685169078272

def entry23 : Entry := ⟨cell23, certificate23⟩

def entries : List Entry := [entry20, entry21, entry22, entry23]

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

end ConstantDirectCover128Shard05
end SparseThresholdDominant
end CertifiedJL
