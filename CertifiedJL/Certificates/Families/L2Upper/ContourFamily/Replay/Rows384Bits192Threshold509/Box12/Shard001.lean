/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 12.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_12_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      108981369231202817405930395487240129186387587898294955497791634344167565195198006259167641987838442984745895576453866403680397934⟩ := by
  decide +kernel

theorem box_12_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      69860273997422026696302786441263647884527165967993125264776981642557493576988769418240482458642313294224629852598317654⟩ := by
  decide +kernel

theorem box_12_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      106246080573124770934783436659539393644237587835090148632851146063591536860164842951667718952305723652745295451⟩ := by
  decide +kernel

theorem box_12_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      5864711320186094698195596902566827143336054402707276132759266779512073452851141326037156294536⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
