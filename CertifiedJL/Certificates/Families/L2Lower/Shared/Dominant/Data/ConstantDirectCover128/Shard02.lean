-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard02

open ConstantNumeric

def cell8 : Cell where
  lower := 0
  upper := 1 / 256
  thresholdUpper := 3125 / 3136
  modulusLower := 747 / 250
  z := 81 / 20

def certificate8 : Certificate where
  inactiveUpper := 1000321 / 1000000
  activeUpper := 18757 / 1000000
  growthUpper := 681224568813159853426602778201848015309137644617728

def entry8 : Entry := ⟨cell8, certificate8⟩

def cell9 : Cell where
  lower := 3 / 128
  upper := 1 / 32
  thresholdUpper := 19375 / 19208
  modulusLower := 747 / 250
  z := 49 / 20

def certificate9 : Certificate where
  inactiveUpper := 972873 / 1000000
  activeUpper := 102441 / 1000000
  growthUpper := 13465449827449640848579262152704

def entry9 : Entry := ⟨cell9, certificate9⟩

def cell10 : Cell where
  lower := 3 / 256
  upper := 7 / 512
  thresholdUpper := 44375 / 43904
  modulusLower := 3013 / 1000
  z := 31 / 10

def certificate10 : Certificate where
  inactiveUpper := 982669 / 1000000
  activeUpper := 12693 / 250000
  growthUpper := 2925819403642204682270889536481361133568

def entry10 : Entry := ⟨cell10, certificate10⟩

def cell11 : Cell where
  lower := 13 / 1024
  upper := 7 / 512
  thresholdUpper := 311875 / 307328
  modulusLower := 3019 / 1000
  z := 31 / 10

def certificate11 : Certificate where
  inactiveUpper := 981237 / 1000000
  activeUpper := 3169 / 62500
  growthUpper := 4217431363288472166500465437128087568384

def entry11 : Entry := ⟨cell11, certificate11⟩

def entries : List Entry := [entry8, entry9, entry10, entry11]

end ConstantDirectCover128Shard02
end SparseThresholdDominant
end CertifiedJL
