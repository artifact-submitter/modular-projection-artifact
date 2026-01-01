/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 32.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_32_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 32 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      124328789144019210279080008597804582425574066734850229503674765077661449004440790095809113521413770611592423908400848754890519752289424172851022752806708⟩ := by
  decide +kernel

theorem box_32_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 32 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      26734531409735657926321839351304816657305893639038454278832015985595423160188366345094363750369125829769⟩ := by
  decide +kernel

theorem box_32_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 32 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      47872289085874411228870100776571198686928832584746797545828346654309473605545051194052018412016006522393399770468569191632668028670250531631489693059132⟩ := by
  decide +kernel

theorem box_32_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 32 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      2164736366567986170823204999574980527312996914741597624702851327164705879347859973543538394656117244405503879202691051716259876208408309356340759497583⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
