-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard28

open ConstantNumeric

def cell112 : Cell where
  lower := 7 / 256
  upper := 1 / 32
  thresholdUpper := 78125 / 76832
  modulusLower := 3013 / 1000
  z := 49 / 20

def certificate112 : Certificate where
  inactiveUpper := 968501 / 1000000
  activeUpper := 25501 / 250000
  growthUpper := 24000932748006994058083685105664

def entry112 : Entry := ⟨cell112, certificate112⟩

def cell113 : Cell where
  lower := 9 / 256
  upper := 5 / 128
  thresholdUpper := 5625 / 5488
  modulusLower := 121 / 40
  z := 12 / 5

def certificate113 : Certificate where
  inactiveUpper := 960739 / 1000000
  activeUpper := 55511 / 500000
  growthUpper := 9678056418181338969948284780544

def entry113 : Entry := ⟨cell113, certificate113⟩

def cell114 : Cell where
  lower := 1 / 32
  upper := 5 / 128
  thresholdUpper := 19375 / 19208
  modulusLower := 747 / 250
  z := 12 / 5

def certificate114 : Certificate where
  inactiveUpper := 964919 / 1000000
  activeUpper := 55747 / 500000
  growthUpper := 3119024855032161053554925109248

def entry114 : Entry := ⟨cell114, certificate114⟩

def cell115 : Cell where
  lower := 1 / 64
  upper := 5 / 256
  thresholdUpper := 76875 / 76832
  modulusLower := 747 / 250
  z := 53 / 20

def certificate115 : Certificate where
  inactiveUpper := 245071 / 250000
  activeUpper := 79941 / 1000000
  growthUpper := 2503406328766926923534458513522688

def entry115 : Entry := ⟨cell115, certificate115⟩

def entries : List Entry := [entry112, entry113, entry114, entry115]

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

end ConstantDirectCover128Shard28
end SparseThresholdDominant
end CertifiedJL
