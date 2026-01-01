-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard26

open ConstantNumeric

def cell104 : Cell where
  lower := 11 / 512
  upper := 3 / 128
  thresholdUpper := 78125 / 76832
  modulusLower := 3019 / 1000
  z := 51 / 20

def certificate104 : Certificate where
  inactiveUpper := 48703 / 50000
  activeUpper := 89269 / 1000000
  growthUpper := 458012546521822430648672834289664

def entry104 : Entry := ⟨cell104, certificate104⟩

def cell105 : Cell where
  lower := 1 / 4
  upper := 3 / 8
  thresholdUpper := 3125 / 4802
  modulusLower := 541 / 250
  z := 87 / 20

def certificate105 : Certificate where
  inactiveUpper := 725723 / 1000000
  activeUpper := 149051 / 500000
  growthUpper := 454565667894754994725778152482668544

def entry105 : Entry := ⟨cell105, certificate105⟩

def cell106 : Cell where
  lower := 7 / 128
  upper := 1 / 16
  thresholdUpper := 2500 / 2401
  modulusLower := 3037 / 1000
  z := 49 / 20

def certificate106 : Certificate where
  inactiveUpper := 234907 / 250000
  activeUpper := 59911 / 500000
  growthUpper := 135909521026720658266858721378304

def entry106 : Entry := ⟨cell106, certificate106⟩

def cell107 : Cell where
  lower := 1 / 32
  upper := 3 / 64
  thresholdUpper := 38125 / 38416
  modulusLower := 741 / 250
  z := 5 / 2

def certificate107 : Certificate where
  inactiveUpper := 60223 / 62500
  activeUpper := 26769 / 250000
  growthUpper := 17871590081541671462178322907136

def entry107 : Entry := ⟨cell107, certificate107⟩

def entries : List Entry := [entry104, entry105, entry106, entry107]

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

end ConstantDirectCover128Shard26
end SparseThresholdDominant
end CertifiedJL
