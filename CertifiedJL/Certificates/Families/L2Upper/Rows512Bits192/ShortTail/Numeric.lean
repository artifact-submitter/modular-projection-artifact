import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Core

namespace CertifiedJL.SparseUpperContour.ShortTail

/-- Retain only the initial chunks; every chunk covers one quarter unit. -/
def plan (count : ℕ) : List (ℕ × ℕ) := boxChunkPlan.take count

def computedChunks (box : ProfileBox) (count : ℕ) :=
  (plan count).map fun chunk => boxCellChunk box chunk.1 chunk.2

def integralFrom (box : ProfileBox) (count : ℕ)
    (chunks : List (Interval contourPrecision)) : Interval contourPrecision :=
  let cutoff : ℚ := count / 4
  let alpha := box.sigma * box.sigma / 2
  let cap := realCapUpper contourPrecision box.profileLeft box.lam
  let cells := chunks.foldl (· + ·) (UpperContourKernel.zero contourPrecision)
  let tail := cap.squareN 9 *
    Exp.negUpper contourPrecision (alpha * cutoff * cutoff) 28 *
    UpperContourKernel.frac contourPrecision (1 / (2 * (alpha * cutoff * cutoff)))
  cells + tail

def boundFrom (box : ProfileBox) (count : ℕ)
    (chunks : List (Interval contourPrecision)) : Interval contourPrecision :=
  boxPrefactor box * integralFrom box count chunks

def check (box : ProfileBox) (count : ℕ)
    (chunks : List (Interval contourPrecision)) : Bool :=
  Interval.upperLTCheck (boundFrom box count chunks) box.target

end CertifiedJL.SparseUpperContour.ShortTail
