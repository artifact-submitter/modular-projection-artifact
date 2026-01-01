import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.TaylorNumeric
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box00

/-! Emit matched first-200-cell checks against the same frozen upper endpoints. -/

open CertifiedJL

def main (args : List String) : IO Unit := do
  let evaluator ← match args with
    | ["legacy"] => pure "boxCellChunk"
    | ["taylor"] => pure "TaylorCells.chunk"
    | _ => throw (IO.userError "usage: GenerateUpperTaylorBench.lean legacy|taylor")
  IO.println "import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.TaylorNumeric"
  IO.println "open CertifiedJL CertifiedJL.SparseUpperContour CertifiedJL.SparseUpperContour.ShortTail"
  IO.println "set_option maxRecDepth 1000000"
  IO.println "set_option maxHeartbeats 40000000"
  for (raw, index) in (SparseUpperContourData.Box00.chunks.take 8).zipIdx do
    IO.println s!"theorem chunk_{index} : ({evaluator} (profileBox 0) {25 * index} 25).hi ≤ {raw.hi} := by"
    IO.println "  decide +kernel"
