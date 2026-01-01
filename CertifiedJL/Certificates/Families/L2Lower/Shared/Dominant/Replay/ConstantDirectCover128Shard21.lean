-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard21

open ConstantNumeric

def cell84 : Cell where
  lower := 3 / 512
  upper := 1 / 128
  thresholdUpper := 76875 / 76832
  modulusLower := 1497 / 500
  z := 37 / 10

def certificate84 : Certificate where
  inactiveUpper := 989669 / 1000000
  activeUpper := 5487 / 200000
  growthUpper := 42677546867650846908475994349564452050728648704

def entry84 : Entry := ⟨cell84, certificate84⟩

def cell85 : Cell where
  lower := 5 / 256
  upper := 11 / 512
  thresholdUpper := 78125 / 76832
  modulusLower := 3019 / 1000
  z := 51 / 20

def certificate85 : Certificate where
  inactiveUpper := 24409 / 25000
  activeUpper := 88271 / 1000000
  growthUpper := 458012546521822430648672834289664

def entry85 : Entry := ⟨cell85, certificate85⟩

def cell86 : Cell where
  lower := 15 / 512
  upper := 1 / 32
  thresholdUpper := 158125 / 153664
  modulusLower := 3037 / 1000
  z := 49 / 20

def certificate86 : Certificate where
  inactiveUpper := 966337 / 1000000
  activeUpper := 50889 / 500000
  growthUpper := 57113529692850527089983320227840

def entry86 : Entry := ⟨cell86, certificate86⟩

def cell87 : Cell where
  lower := 3 / 256
  upper := 1 / 64
  thresholdUpper := 76875 / 76832
  modulusLower := 747 / 250
  z := 27 / 10

def certificate87 : Certificate where
  inactiveUpper := 492449 / 500000
  activeUpper := 18637 / 250000
  growthUpper := 10680972066000752489220147827965952

def entry87 : Entry := ⟨cell87, certificate87⟩

def entries : List Entry := [entry84, entry85, entry86, entry87]

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

end ConstantDirectCover128Shard21
end SparseThresholdDominant
end CertifiedJL
