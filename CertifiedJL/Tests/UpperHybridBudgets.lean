/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Core
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box09
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box10
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box11
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box12
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box13
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box14
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box15
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box16
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box17

/-! Cheap exact checks against all original hybrid probability budgets.
Frozen chunks are inputs, not certified here; no numerical leaf is imported. -/
namespace CertifiedJL.SparseUpperHybrid.BudgetTests

def frozenChunks : List (List (Interval precision)) :=
  [SparseUpperHybridGenerated.Box00.chunks,
   SparseUpperHybridGenerated.Box01.chunks,
   SparseUpperHybridGenerated.Box02.chunks,
   SparseUpperHybridGenerated.Box03.chunks,
   SparseUpperHybridGenerated.Box04.chunks,
   SparseUpperHybridGenerated.Box05.chunks,
   SparseUpperHybridGenerated.Box06.chunks,
   SparseUpperHybridGenerated.Box07.chunks,
   SparseUpperHybridGenerated.Box08.chunks,
   SparseUpperHybridGenerated.Box09.chunks,
   SparseUpperHybridGenerated.Box10.chunks,
   SparseUpperHybridGenerated.Box11.chunks,
   SparseUpperHybridGenerated.Box12.chunks,
   SparseUpperHybridGenerated.Box13.chunks,
   SparseUpperHybridGenerated.Box14.chunks,
   SparseUpperHybridGenerated.Box15.chunks,
   SparseUpperHybridGenerated.Box16.chunks,
   SparseUpperHybridGenerated.Box17.chunks]

set_option maxRecDepth 100000 in
theorem all_eighteen_targets :
    (certificateBoxes.zip frozenChunks).all (fun pair =>
      Interval.upperLTCheck (boxBoundFrom pair.1.box pair.2) 1) = true := by
  decide +kernel

theorem full_box_count : certificateBoxes.length = 18 ∧ frozenChunks.length = 18 := by
  decide +kernel

theorem active_work_counts : certificateCellCount = 5049 ∧
    (certificateBoxes.map (fun c => (certificateChunkPlan c).length)).sum = 523 := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.BudgetTests
