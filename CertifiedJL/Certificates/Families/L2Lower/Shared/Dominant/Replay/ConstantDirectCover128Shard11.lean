-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard11

open ConstantNumeric

def cell44 : Cell where
  lower := 19 / 1024
  upper := 5 / 256
  thresholdUpper := 156875 / 153664
  modulusLower := 757 / 250
  z := 13 / 5

def certificate44 : Certificate where
  inactiveUpper := 977081 / 1000000
  activeUpper := 20833 / 250000
  growthUpper := 2718876775192443208944414816731136

def entry44 : Entry := ⟨cell44, certificate44⟩

def cell45 : Cell where
  lower := 3 / 512
  upper := 1 / 128
  thresholdUpper := 154375 / 153664
  modulusLower := 3
  z := 18 / 5

def certificate45 : Certificate where
  inactiveUpper := 15468 / 15625
  activeUpper := 15069 / 500000
  growthUpper := 3584710383175820693429017848424892592960831488

def entry45 : Entry := ⟨cell45, certificate45⟩

def cell46 : Cell where
  lower := 7 / 1024
  upper := 1 / 128
  thresholdUpper := 19375 / 19208
  modulusLower := 3009 / 1000
  z := 18 / 5

def certificate46 : Certificate where
  inactiveUpper := 247063 / 250000
  activeUpper := 3009 / 100000
  growthUpper := 5481097991653162400317119317340315297981136896

def entry46 : Entry := ⟨cell46, certificate46⟩

def cell47 : Cell where
  lower := 1 / 64
  upper := 17 / 1024
  thresholdUpper := 78125 / 76832
  modulusLower := 1511 / 500
  z := 53 / 20

def certificate47 : Certificate where
  inactiveUpper := 980273 / 1000000
  activeUpper := 15647 / 200000
  growthUpper := 8740305844523062814803878320537600

def entry47 : Entry := ⟨cell47, certificate47⟩

def entries : List Entry := [entry44, entry45, entry46, entry47]

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

end ConstantDirectCover128Shard11
end SparseThresholdDominant
end CertifiedJL
