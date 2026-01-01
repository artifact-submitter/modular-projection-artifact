-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard38

open ConstantNumeric

def cell152 : Cell where
  lower := 7 / 16
  upper := 1 / 2
  thresholdUpper := 9375 / 9604
  modulusLower := 2863 / 1000
  z := 14 / 5

def certificate152 : Certificate where
  inactiveUpper := 692691 / 1000000
  activeUpper := 4113 / 12500
  growthUpper := 26802379169318174979036139116036096

def entry152 : Entry := ⟨cell152, certificate152⟩

def cell153 : Cell where
  lower := 7 / 16
  upper := 1 / 2
  thresholdUpper := 1875 / 2401
  modulusLower := 121 / 50
  z := 71 / 20

def certificate153 : Certificate where
  inactiveUpper := 331437 / 500000
  activeUpper := 44281 / 125000
  growthUpper := 83165396172990300375479014435848192

def entry153 : Entry := ⟨cell153, certificate153⟩

def cell154 : Cell where
  lower := 7 / 16
  upper := 15 / 32
  thresholdUpper := 9375 / 19208
  modulusLower := 253 / 125
  z := 101 / 20

def certificate154 : Certificate where
  inactiveUpper := 622249 / 1000000
  activeUpper := 86177 / 200000
  growthUpper := 11149600685502595205002923343872

def entry154 : Entry := ⟨cell154, certificate154⟩

def cell155 : Cell where
  lower := 1 / 8
  upper := 1 / 4
  thresholdUpper := 1875 / 2401
  modulusLower := 121 / 50
  z := 69 / 20

def certificate155 : Certificate where
  inactiveUpper := 211117 / 250000
  activeUpper := 9047 / 50000
  growthUpper := 8637817676496999277283087132655616

def entry155 : Entry := ⟨cell155, certificate155⟩

def entries : List Entry := [entry152, entry153, entry154, entry155]

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

end ConstantDirectCover128Shard38
end SparseThresholdDominant
end CertifiedJL
