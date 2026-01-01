-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard23

open ConstantNumeric

def cell92 : Cell where
  lower := 19 / 512
  upper := 5 / 128
  thresholdUpper := 159375 / 153664
  modulusLower := 3049 / 1000
  z := 12 / 5

def certificate92 : Certificate where
  inactiveUpper := 95867 / 100000
  activeUpper := 55393 / 500000
  growthUpper := 22626383036822706586564153049088

def entry92 : Entry := ⟨cell92, certificate92⟩

def cell93 : Cell where
  lower := 1 / 32
  upper := 9 / 256
  thresholdUpper := 5625 / 5488
  modulusLower := 121 / 40
  z := 12 / 5

def certificate93 : Certificate where
  inactiveUpper := 964901 / 1000000
  activeUpper := 27173 / 250000
  growthUpper := 9678056418181338969948284780544

def entry93 : Entry := ⟨cell93, certificate93⟩

def cell94 : Cell where
  lower := 5 / 128
  upper := 11 / 256
  thresholdUpper := 79375 / 76832
  modulusLower := 3037 / 1000
  z := 47 / 20

def certificate94 : Certificate where
  inactiveUpper := 957483 / 1000000
  activeUpper := 118087 / 1000000
  growthUpper := 3811561968467702423709097656320

def entry94 : Entry := ⟨cell94, certificate94⟩

def cell95 : Cell where
  lower := 0
  upper := 1 / 32
  thresholdUpper := 625 / 686
  modulusLower := 2759 / 1000
  z := 13 / 5

def certificate95 : Certificate where
  inactiveUpper := 500209 / 500000
  activeUpper := 91087 / 1000000
  growthUpper := 689170084081820343983377743872

def entry95 : Entry := ⟨cell95, certificate95⟩

def entries : List Entry := [entry92, entry93, entry94, entry95]

end ConstantDirectCover128Shard23
end SparseThresholdDominant
end CertifiedJL
