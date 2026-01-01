/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.ShortTail.Numeric
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Data.Box09

/-!
Exact feasibility check for replacing late contour rectangles by the closed
Gaussian tail. This checks budgets from frozen raw endpoints, NOT the correctness
of those endpoints or the semantic integral bound. No expensive replay is imported.
-/

namespace CertifiedJL.SparseUpperContour.ShortTailExperiment

def retainedChunks : List ℕ := [15, 12, 10, 9, 8, 7, 6, 5, 4, 3]

def frozenChunks : List (List (Interval 512)) :=
  [SparseUpperContourData.Box00.chunks, SparseUpperContourData.Box01.chunks,
   SparseUpperContourData.Box02.chunks, SparseUpperContourData.Box03.chunks,
   SparseUpperContourData.Box04.chunks, SparseUpperContourData.Box05.chunks,
   SparseUpperContourData.Box06.chunks, SparseUpperContourData.Box07.chunks,
   SparseUpperContourData.Box08.chunks, SparseUpperContourData.Box09.chunks]

def shortTailBound (box : ProfileBox) (chunks : List (Interval 512))
    (count : ℕ) : Interval 512 :=
  ShortTail.boundFrom box count (chunks.take count)

def budgetCheck (index : ℕ) : Bool :=
  match profileBoxes[index]?, frozenChunks[index]?, retainedChunks[index]? with
  | some box, some chunks, some count =>
    decide (0 < count ∧ count ≤ chunks.length) &&
      Interval.upperLTCheck (shortTailBound box chunks count) box.target
  | _, _, _ => false

set_option maxRecDepth 100000 in
theorem all_ten_original_targets : (List.range 10).all budgetCheck = true := by
  decide +kernel

theorem retained_cell_count : retainedChunks.sum * 25 = 1975 := by decide +kernel

end CertifiedJL.SparseUpperContour.ShortTailExperiment
