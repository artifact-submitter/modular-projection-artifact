import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Numeric
import CertifiedJL.Arithmetic.Transcendental.Exponential.TaylorExpData

namespace CertifiedJL.SparseUpperContour.ShortTail.TaylorCells

/-- Candidate evaluator with a Taylor weight and an ordered row interval. -/
def gaussianCell (box : ProfileBox) (mesh : ℚ) (index : ℕ) : Interval contourPrecision :=
  let frequencyLeft := index * mesh
  let frequencyRight := (index + 1) * mesh
  let expressionLeft := rowExpressionOnCell box.profileLeft
    frequencyLeft frequencyRight box.lam
  let expressionRight := rowExpressionOnCell box.profileRight
    frequencyLeft frequencyRight box.lam
  let cap := realCapUpper contourPrecision box.profileLeft box.lam
  let rowUpper := min cap.hi (max expressionLeft.hi expressionRight.hi)
  let alpha := box.sigma * box.sigma / 2
  let weight := TaylorExp.negUpper contourPrecision
    (alpha * frequencyLeft * frequencyLeft) 10
  UpperContourKernel.frac contourPrecision mesh * weight *
    (Interval.mk (min 0 rowUpper) rowUpper).squareN 9 *
    UpperContourKernel.inverseSqrtAtLeft contourPrecision frequencyLeft box.lam

def chunk (box : ProfileBox) (start count : ℕ) : Interval contourPrecision :=
  (List.range count).foldl
    (fun total offset => total + gaussianCell box (1 / 100) (start + offset))
    (UpperContourKernel.zero contourPrecision)

end CertifiedJL.SparseUpperContour.ShortTail.TaylorCells
