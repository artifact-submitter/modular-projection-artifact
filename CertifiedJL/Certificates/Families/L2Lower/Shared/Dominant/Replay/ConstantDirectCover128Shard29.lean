-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard29

open ConstantNumeric

def cell116 : Cell where
  lower := 13 / 256
  upper := 7 / 128
  thresholdUpper := 2500 / 2401
  modulusLower := 3049 / 1000
  z := 49 / 20

def certificate116 : Certificate where
  inactiveUpper := 58973 / 62500
  activeUpper := 5779 / 50000
  growthUpper := 135909521026720658266858721378304

def entry116 : Entry := ⟨cell116, certificate116⟩

def cell117 : Cell where
  lower := 1 / 256
  upper := 1 / 128
  thresholdUpper := 75625 / 76832
  modulusLower := 741 / 250
  z := 31 / 10

def certificate117 : Certificate where
  inactiveUpper := 99433 / 100000
  activeUpper := 24249 / 500000
  growthUpper := 271671584833487030654565208445209804800

def entry117 : Entry := ⟨cell117, certificate117⟩

def cell118 : Cell where
  lower := 3 / 64
  upper := 1 / 16
  thresholdUpper := 19375 / 19208
  modulusLower := 741 / 250
  z := 49 / 20

def certificate118 : Certificate where
  inactiveUpper := 473829 / 500000
  activeUpper := 2399 / 20000
  growthUpper := 13465449827449640848579262152704

def entry118 : Entry := ⟨cell118, certificate118⟩

def cell119 : Cell where
  lower := 3 / 64
  upper := 7 / 128
  thresholdUpper := 5625 / 5488
  modulusLower := 3013 / 1000
  z := 49 / 20

def certificate119 : Certificate where
  inactiveUpper := 947609 / 1000000
  activeUpper := 115623 / 1000000
  growthUpper := 42779467463469489459418831519744

def entry119 : Entry := ⟨cell119, certificate119⟩

def entries : List Entry := [entry116, entry117, entry118, entry119]

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

end ConstantDirectCover128Shard29
end SparseThresholdDominant
end CertifiedJL
