-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard18

open ConstantNumeric

def cell72 : Cell where
  lower := 0
  upper := 1 / 256
  thresholdUpper := 38125 / 38416
  modulusLower := 372 / 125
  z := 17 / 4

def certificate72 : Certificate where
  inactiveUpper := 500161 / 500000
  activeUpper := 1549 / 100000
  growthUpper := 133552637446126801521225709025967335307469959259488256

def entry72 : Entry := ⟨cell72, certificate72⟩

def cell73 : Cell where
  lower := 1 / 512
  upper := 1 / 256
  thresholdUpper := 76875 / 76832
  modulusLower := 1497 / 500
  z := 43 / 10

def certificate73 : Certificate where
  inactiveUpper := 996149 / 1000000
  activeUpper := 14723 / 1000000
  growthUpper := 1552932750789441734288484652309375321796193129395650560

def entry73 : Entry := ⟨cell73, certificate73⟩

def cell74 : Cell where
  lower := 27 / 1024
  upper := 7 / 256
  thresholdUpper := 158125 / 153664
  modulusLower := 76 / 25
  z := 5 / 2

def certificate74 : Certificate where
  inactiveUpper := 38759 / 40000
  activeUpper := 3811 / 40000
  growthUpper := 253949594666790579868325319278592

def entry74 : Entry := ⟨cell74, certificate74⟩

def cell75 : Cell where
  lower := 13 / 512
  upper := 7 / 256
  thresholdUpper := 5625 / 5488
  modulusLower := 3031 / 1000
  z := 5 / 2

def certificate75 : Certificate where
  inactiveUpper := 485043 / 500000
  activeUpper := 4769 / 50000
  growthUpper := 189096111593227172226989513768960

def entry75 : Entry := ⟨cell75, certificate75⟩

def entries : List Entry := [entry72, entry73, entry74, entry75]

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

end ConstantDirectCover128Shard18
end SparseThresholdDominant
end CertifiedJL
