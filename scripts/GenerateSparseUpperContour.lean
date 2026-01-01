/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Core

/-!
# Generate all ten sparse U14 profile boxes

The default mode deterministically emits the ten raw per-box payloads.
`--check` compares every expected output byte-for-byte and rejects unexpected
generated data topology. The active short-tail replay is generated separately
from these preserved endpoints.
-/

open CertifiedJL
open CertifiedJL.SparseUpperContour

namespace GenerateSparseUpperContour

def boxCount : ℕ := profileBoxes.length

def dataDirectory : String :=
  "CertifiedJL/Certificates/Families/L2Upper/Rows512Bits192/Data"

def pad2 (n : ℕ) : String :=
  let digits := toString n
  String.ofList (List.replicate (2 - digits.length) '0') ++ digits

def intervalLiteral (I : UpperContourKernel.DInterval contourPrecision) : String :=
  s!"⟨{I.lo},\n        {I.hi}⟩"

def chunksForBox (boxIndex : ℕ) :
    List (UpperContourKernel.DInterval contourPrecision) :=
  let box := profileBox boxIndex
  boxChunkPlan.map fun chunk => boxCellChunk box chunk.1 chunk.2

def allChunks : List (List (UpperContourKernel.DInterval contourPrecision)) :=
  (List.range boxCount).map chunksForBox

def expectedBounds
    (generated : List (List (UpperContourKernel.DInterval contourPrecision))) :
    List (UpperContourKernel.DInterval contourPrecision) :=
  (List.range boxCount).map fun boxIndex =>
    let box := profileBox boxIndex
    boxPrefactor box * boxIntegralFrom box (generated.getD boxIndex [])

def copyrightHeader : String :=
  "/-\n" ++
  "Copyright (c) 2026 Anonymous Author. All rights reserved.\n" ++
  "Released under Apache 2.0 license as described in the file LICENSE.\n" ++
  "Authors: Anonymous Author\n" ++
  "-/\n\n"

def chunkListLiteral
    (chunks : List (UpperContourKernel.DInterval contourPrecision)) : String :=
  let entries := chunks.map fun I => "      " ++ intervalLiteral I
  "[\n" ++ String.intercalate ",\n" entries ++ "\n    ]"

def boxDataPath (boxIndex : ℕ) : String :=
  s!"{dataDirectory}/Box{pad2 boxIndex}.lean"

def boxDataSource
    (generated : List (List (UpperContourKernel.DInterval contourPrecision)))
    (boxIndex : ℕ) : String :=
  let chunks := generated.getD boxIndex []
  let bound := (expectedBounds generated).getD boxIndex ⟨0, 0⟩
  copyrightHeader ++
  "import CertifiedJL.Arithmetic.Interval.Interval\n\n" ++
  s!"/-! Raw endpoints for sparse U14 box {boxIndex}. -/\n\n" ++
  s!"namespace CertifiedJL\nnamespace SparseUpperContourData\nnamespace Box{pad2 boxIndex}\n\n" ++
  "set_option linter.style.longLine false\n\n" ++
  s!"def chunks : List (Interval {contourPrecision}) :=\n    " ++
  chunkListLiteral chunks ++ "\n\n" ++
  s!"def expectedBound : Interval {contourPrecision} :=\n  " ++
  intervalLiteral bound ++
  s!"\n\nend Box{pad2 boxIndex}\nend SparseUpperContourData\nend CertifiedJL\n"

def ensureDirectories : IO Unit := do
  IO.FS.createDirAll "CertifiedJL/Certificates/Families/L2Upper/Rows512Bits192"
  IO.FS.createDirAll dataDirectory

def generateData
    (generated : List (List (UpperContourKernel.DInterval contourPrecision))) : IO Unit := do
  ensureDirectories
  for boxIndex in List.range boxCount do
    IO.FS.writeFile (boxDataPath boxIndex) (boxDataSource generated boxIndex)
  IO.println s!"generated per-box data in {dataDirectory}"

def generateAll : IO Unit :=
  generateData allChunks

private def checkSource (path expected : String) : IO Unit := do
  let actual ← IO.FS.readFile path
  unless actual == expected do
    throw <| IO.userError s!"generated source differs: {path}"

def checkAll : IO Unit := do
  let generated := allChunks
  for boxIndex in List.range boxCount do
    checkSource (boxDataPath boxIndex) (boxDataSource generated boxIndex)
  let dataEntries ← System.FilePath.readDir dataDirectory
  unless dataEntries.size == boxCount do
    throw <| IO.userError
      s!"expected {boxCount} generated data files, found {dataEntries.size}"
  IO.println s!"sparse upper-contour data check passed: {boxCount} boxes"

end GenerateSparseUpperContour

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [] => GenerateSparseUpperContour.generateAll
  | ["--check"] => GenerateSparseUpperContour.checkAll
  | ["data"] =>
      GenerateSparseUpperContour.generateData GenerateSparseUpperContour.allChunks
  | _ => throw (IO.userError
      "usage: GenerateSparseUpperContour [--check|data]")
