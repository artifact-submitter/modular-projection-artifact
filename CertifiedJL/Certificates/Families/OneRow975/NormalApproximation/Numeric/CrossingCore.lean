import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.ElementaryCore

namespace CertifiedJL.TyurinModerate

/-- A quadratic coefficient dominating both Tyurin density branches up to
the cutoff, including the short region beyond their tangent switch. -/
def crossingCoreCap (C : Cell) : ℚ :=
  max (varianceCapInterval C).upperRat
    (2 * C.hi * C.cutoff / 5 + 25 / (27 * C.cutoff ^ 2))

/-- Closed Gaussian-moment budget for a cell that crosses the switch. -/
def crossingCoreIntegral (C : Cell) : ℚ :=
  C.hi * (513 / 500) / (2 * piLower) * sqrtTwoPiUpper / 2 *
    (1071 / 16384 + (1681 / 16384) / (1 - crossingCoreCap C) ^ 2)

end CertifiedJL.TyurinModerate
