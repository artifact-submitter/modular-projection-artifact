/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      3332768528038067375590577529282287750142140966255543562743446941854330688786016547798770483775675134113222583468607386⟩ := by
  decide +kernel

theorem box_04_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      65055772680717090260845735860080127487424505896046938407891267750346358837683690829951288831203814380⟩ := by
  decide +kernel

theorem box_04_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      42443407951405168403939764324028993289863137881321760173760419629568652905760274260358607910039285419275445578738482087124907370014857008968418721871355⟩ := by
  decide +kernel

theorem box_04_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      41770956118656253922307429596765073696820954785370873702573563089063312826762861292866189054630012278511290074820521292021173130351768907852571879067985⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
