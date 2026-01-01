-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard40

open ConstantNumeric

def cell160 : Cell where
  lower := 7 / 16
  upper := 1 / 2
  thresholdUpper := 1875 / 4802
  modulusLower := 2
  z := 27 / 5

def certificate160 : Certificate where
  inactiveUpper := 313561 / 500000
  activeUpper := 14529 / 31250
  growthUpper := 362964645222424103868170240

def entry160 : Entry := ⟨cell160, certificate160⟩

def cell161 : Cell where
  lower := 3 / 32
  upper := 1 / 8
  thresholdUpper := 9375 / 9604
  modulusLower := 2863 / 1000
  z := 53 / 20

def certificate161 : Certificate where
  inactiveUpper := 896267 / 1000000
  activeUpper := 137811 / 1000000
  growthUpper := 383741191489060025394192208363520

def entry161 : Entry := ⟨cell161, certificate161⟩

def cell162 : Cell where
  lower := 31 / 64
  upper := 1 / 2
  thresholdUpper := 9375 / 19208
  modulusLower := 103 / 50
  z := 49 / 10

def certificate162 : Certificate where
  inactiveUpper := 19119 / 31250
  activeUpper := 222293 / 500000
  growthUpper := 1334110647185013930375384137728

def entry162 : Entry := ⟨cell162, certificate162⟩

def cell163 : Cell where
  lower := 0
  upper := 1 / 32
  thresholdUpper := 8125 / 9604
  modulusLower := 2651 / 1000
  z := 13 / 4

def certificate163 : Certificate where
  inactiveUpper := 1000457 / 1000000
  activeUpper := 52843 / 1000000
  growthUpper := 42961281505528073539428163872882688

def entry163 : Entry := ⟨cell163, certificate163⟩

def entries : List Entry := [entry160, entry161, entry162, entry163]

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

end ConstantDirectCover128Shard40
end SparseThresholdDominant
end CertifiedJL
