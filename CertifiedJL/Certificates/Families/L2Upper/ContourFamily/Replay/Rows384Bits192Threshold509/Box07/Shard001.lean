/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      59604628334098924761203155942944880675701541093384337399582500213998632818459388214062723052133002516037214562685552254112735652⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      31502209176811732348409959531857959463235217279286818174695106415631992231803029410383628156437838764959493892706740774⟩ := by
  decide +kernel

theorem box_07_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      35115079349214536299583641097607201800333096734028162315656354838217073520151610642524927176666854228724706851⟩ := by
  decide +kernel

theorem box_07_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 7 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      484883363768930665017631265630174695709904847341599747233319216861728727707041989907045674706⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
