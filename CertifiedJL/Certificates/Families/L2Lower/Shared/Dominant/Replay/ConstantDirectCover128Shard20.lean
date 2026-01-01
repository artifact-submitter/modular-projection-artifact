-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard20

open ConstantNumeric

def cell80 : Cell where
  lower := 29 / 1024
  upper := 15 / 512
  thresholdUpper := 316875 / 307328
  modulusLower := 3043 / 1000
  z := 49 / 20

def certificate80 : Certificate where
  inactiveUpper := 967409 / 1000000
  activeUpper := 50293 / 500000
  growthUpper := 65991927651521830458353038393344

def entry80 : Entry := ⟨cell80, certificate80⟩

def cell81 : Cell where
  lower := 1 / 256
  upper := 1 / 128
  thresholdUpper := 38125 / 38416
  modulusLower := 372 / 125
  z := 37 / 10

def certificate81 : Certificate where
  inactiveUpper := 993187 / 1000000
  activeUpper := 1101 / 40000
  growthUpper := 17829011638720197382604133366317628073202155520

def entry81 : Entry := ⟨cell81, certificate81⟩

def cell82 : Cell where
  lower := 0
  upper := 1 / 128
  thresholdUpper := 9375 / 9604
  modulusLower := 2939 / 1000
  z := 15 / 4

def certificate82 : Certificate where
  inactiveUpper := 1000337 / 1000000
  activeUpper := 412 / 15625
  growthUpper := 12814290107724482313167944911790724276333576192

def entry82 : Entry := ⟨cell82, certificate82⟩

def cell83 : Cell where
  lower := 1 / 128
  upper := 1 / 64
  thresholdUpper := 75625 / 76832
  modulusLower := 741 / 250
  z := 27 / 10

def certificate83 : Certificate where
  inactiveUpper := 98997 / 100000
  activeUpper := 2341 / 31250
  growthUpper := 2987929190421840327718784305463296

def entry83 : Entry := ⟨cell83, certificate83⟩

def entries : List Entry := [entry80, entry81, entry82, entry83]

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

end ConstantDirectCover128Shard20
end SparseThresholdDominant
end CertifiedJL
