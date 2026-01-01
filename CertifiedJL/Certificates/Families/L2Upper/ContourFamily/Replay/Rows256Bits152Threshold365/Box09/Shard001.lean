/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      15574562653944085842646901418313150003655690220200026090589976688974211978131516291803988743145091622421709452362194241190865044982613776⟩ := by
  decide +kernel

theorem box_09_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      37026785601602582441797942742087809583107539868784649337988163709854895258774994651947313427827562571457590344431550729525146374072922300791628309667525⟩ := by
  decide +kernel

theorem box_09_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      70969421947784313410210098988961050884336641134340434059449607405406141979480364447274594057121118200453755025546651277756717781447250657615174679850164⟩ := by
  decide +kernel

theorem box_09_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 9 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      507514312693458962038218993133046257830790658042779555989249728465518904816268852169976002736515592991926425308496497719544630948044238224674645173998⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
