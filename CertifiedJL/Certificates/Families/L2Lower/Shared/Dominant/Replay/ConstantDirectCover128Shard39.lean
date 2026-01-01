-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard39

open ConstantNumeric

def cell156 : Cell where
  lower := 15 / 32
  upper := 1 / 2
  thresholdUpper := 1250 / 2401
  modulusLower := 419 / 200
  z := 19 / 4

def certificate156 : Certificate where
  inactiveUpper := 124173 / 200000
  activeUpper := 214979 / 500000
  growthUpper := 14115987143100592744467141754880

def entry156 : Entry := ⟨cell156, certificate156⟩

def cell157 : Cell where
  lower := 1 / 4
  upper := 3 / 8
  thresholdUpper := 1875 / 2401
  modulusLower := 121 / 50
  z := 73 / 20

def certificate157 : Certificate where
  inactiveUpper := 745967 / 1000000
  activeUpper := 259121 / 1000000
  growthUpper := 800721128836740184603051840357007360

def entry157 : Entry := ⟨cell157, certificate157⟩

def cell158 : Cell where
  lower := 7 / 16
  upper := 15 / 32
  thresholdUpper := 625 / 1372
  modulusLower := 2
  z := 21 / 4

def certificate158 : Certificate where
  inactiveUpper := 309597 / 500000
  activeUpper := 109743 / 250000
  growthUpper := 1334110647185013930375384137728

def entry158 : Entry := ⟨cell158, certificate158⟩

def cell159 : Cell where
  lower := 5 / 32
  upper := 3 / 16
  thresholdUpper := 2500 / 2401
  modulusLower := 741 / 250
  z := 27 / 10

def certificate159 : Certificate where
  inactiveUpper := 841221 / 1000000
  activeUpper := 41933 / 250000
  growthUpper := 258054819570947659825672902626246656

def entry159 : Entry := ⟨cell159, certificate159⟩

def entries : List Entry := [entry156, entry157, entry158, entry159]

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

end ConstantDirectCover128Shard39
end SparseThresholdDominant
end CertifiedJL
