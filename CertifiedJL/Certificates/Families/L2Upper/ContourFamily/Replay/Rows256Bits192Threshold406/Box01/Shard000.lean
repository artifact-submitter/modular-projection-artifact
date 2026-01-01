/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      641215530398940979180030560239897289303551336447504220267607287921180925509434637320448014539354260709803354262203725403811671979896931936395864630668906⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      13402584777565500006186930395812809599354389886687912647392172191435368874381832761830678547487887653881362624846236275787618053886883737645973516890⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3042272342316892123218065744257925850310478028444241458251078946343187086674194441014663802477817010037496872490707825447978861881028131586⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 1 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      27328644965116850389705221367567477489126166069533108516940690853885524605328916541483790860939161945368679894213287934917977790⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
