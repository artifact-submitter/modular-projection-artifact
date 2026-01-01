import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.Core

namespace CertifiedJL.TyurinModerate

/-- Closed Gaussian-moment majorant for cells before the Tyurin switch.
The endpoint variance cap is rounded outward once; no core mesh is evaluated. -/
def closedCoreIntegral (C : Cell) : ℚ :=
  let c := (varianceCapInterval C).upperRat
  C.hi * (513 / 500) / (2 * piLower) * sqrtTwoPiUpper / 2 *
    (1071 / 16384 + (1681 / 16384) / (1 - c) ^ 2)

end CertifiedJL.TyurinModerate
