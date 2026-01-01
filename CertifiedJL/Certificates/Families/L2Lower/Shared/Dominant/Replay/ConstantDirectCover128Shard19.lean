-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard19

open ConstantNumeric

def cell76 : Cell where
  lower := 3 / 128
  upper := 7 / 256
  thresholdUpper := 78125 / 76832
  modulusLower := 3013 / 1000
  z := 5 / 2

def certificate76 : Certificate where
  inactiveUpper := 6077 / 6250
  activeUpper := 11949 / 125000
  growthUpper := 104846212744256242666681254543360

def entry76 : Entry := ⟨cell76, certificate76⟩

def cell77 : Cell where
  lower := 1 / 256
  upper := 3 / 512
  thresholdUpper := 76875 / 76832
  modulusLower := 1497 / 500
  z := 79 / 20

def certificate77 : Certificate where
  inactiveUpper := 496351 / 500000
  activeUpper := 21141 / 1000000
  growthUpper := 60338792541399748960891273692464635214284254609408

def entry77 : Entry := ⟨cell77, certificate77⟩

def cell78 : Cell where
  lower := 0
  upper := 1 / 512
  thresholdUpper := 76875 / 76832
  modulusLower := 1497 / 500
  z := 91 / 20

def certificate78 : Certificate where
  inactiveUpper := 1000313 / 1000000
  activeUpper := 7 / 625
  growthUpper := 2195582782000369880850426985189501182865056117095722385408

def entry78 : Entry := ⟨cell78, certificate78⟩

def cell79 : Cell where
  lower := 19 / 1024
  upper := 5 / 256
  thresholdUpper := 313125 / 307328
  modulusLower := 121 / 40
  z := 13 / 5

def certificate79 : Certificate where
  inactiveUpper := 977081 / 1000000
  activeUpper := 83333 / 1000000
  growthUpper := 2332360961548867473549147909390336

def entry79 : Entry := ⟨cell79, certificate79⟩

def entries : List Entry := [entry76, entry77, entry78, entry79]

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

end ConstantDirectCover128Shard19
end SparseThresholdDominant
end CertifiedJL
