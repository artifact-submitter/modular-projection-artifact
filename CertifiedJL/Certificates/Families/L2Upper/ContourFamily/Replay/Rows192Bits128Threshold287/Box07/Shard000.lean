/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      370375589324252068550755561967049584070412773172606278758676844868286971061033368138493050757938049391542129164960748914227553996068770883643124706805520⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      21943741631884411693856206462377608350844291435475716832509608784365888040560084519273961654687954548857326272788767247522130208265377374025082562080244⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      25080659098905167022751972255736425573603525286644822169950347024902922065090559434429849956333370780238450977029431029920471792961250391213374485386⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      1745190575888406064120343735996153819886376247847701281763637465005125275217538707977441360145813184146984763608240618781971199122667279948198919⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
