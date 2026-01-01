-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard32

open ConstantNumeric

def cell128 : Cell where
  lower := 5 / 128
  upper := 3 / 64
  thresholdUpper := 19375 / 19208
  modulusLower := 747 / 250
  z := 5 / 2

def certificate128 : Certificate where
  inactiveUpper := 954959 / 1000000
  activeUpper := 53521 / 500000
  growthUpper := 58133021531722081612006034505728

def entry128 : Entry := ⟨cell128, certificate128⟩

def cell129 : Cell where
  lower := 5 / 64
  upper := 3 / 32
  thresholdUpper := 2500 / 2401
  modulusLower := 3013 / 1000
  z := 49 / 20

def certificate129 : Certificate where
  inactiveUpper := 916957 / 1000000
  activeUpper := 136883 / 1000000
  growthUpper := 135909521026720658266858721378304

def entry129 : Entry := ⟨cell129, certificate129⟩

def cell130 : Cell where
  lower := 7 / 16
  upper := 1 / 2
  thresholdUpper := 5625 / 9604
  modulusLower := 541 / 250
  z := 87 / 20

def certificate130 : Certificate where
  inactiveUpper := 642809 / 1000000
  activeUpper := 51317 / 125000
  growthUpper := 123671351192531119710377462464512

def entry130 : Entry := ⟨cell130, certificate130⟩

def cell131 : Cell where
  lower := 1 / 32
  upper := 1 / 16
  thresholdUpper := 18125 / 19208
  modulusLower := 2863 / 1000
  z := 5 / 2

def certificate131 : Certificate where
  inactiveUpper := 192733 / 200000
  activeUpper := 115827 / 1000000
  growthUpper := 519259066901237455806374346752

def entry131 : Entry := ⟨cell131, certificate131⟩

def entries : List Entry := [entry128, entry129, entry130, entry131]

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

end ConstantDirectCover128Shard32
end SparseThresholdDominant
end CertifiedJL
