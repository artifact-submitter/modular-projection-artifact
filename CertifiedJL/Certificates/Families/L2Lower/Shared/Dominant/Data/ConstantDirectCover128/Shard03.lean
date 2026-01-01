-- evaluated 403
-- accepted 188
-- worst 1.815240990434
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantDirectCover128Shard03

open ConstantNumeric

def cell12 : Cell where
  lower := 1 / 32
  upper := 17 / 512
  thresholdUpper := 318125 / 307328
  modulusLower := 3049 / 1000
  z := 12 / 5

def certificate12 : Certificate where
  inactiveUpper := 964893 / 1000000
  activeUpper := 10733 / 100000
  growthUpper := 19640112479945484564645713805312

def entry12 : Entry := ⟨cell12, certificate12⟩

def cell13 : Cell where
  lower := 11 / 256
  upper := 3 / 64
  thresholdUpper := 2500 / 2401
  modulusLower := 3049 / 1000
  z := 47 / 20

def certificate13 : Certificate where
  inactiveUpper := 953503 / 1000000
  activeUpper := 120591 / 1000000
  growthUpper := 6635368471505288969685169078272

def entry13 : Entry := ⟨cell13, certificate13⟩

def cell14 : Cell where
  lower := 0
  upper := 1 / 512
  thresholdUpper := 154375 / 153664
  modulusLower := 3
  z := 22 / 5

def certificate14 : Certificate where
  inactiveUpper := 1000313 / 1000000
  activeUpper := 12947 / 1000000
  growthUpper := 47501331663065064295359470467085684007638125618214731776

def entry14 : Entry := ⟨cell14, certificate14⟩

def cell15 : Cell where
  lower := 1 / 512
  upper := 1 / 256
  thresholdUpper := 154375 / 153664
  modulusLower := 3
  z := 81 / 20

def certificate15 : Certificate where
  inactiveUpper := 996389 / 1000000
  activeUpper := 9351 / 500000
  growthUpper := 1771008563985205511689030807544585469649826703474688

def entry15 : Entry := ⟨cell15, certificate15⟩

def entries : List Entry := [entry12, entry13, entry14, entry15]

end ConstantDirectCover128Shard03
end SparseThresholdDominant
end CertifiedJL
