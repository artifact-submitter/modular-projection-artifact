/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 11.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_11_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      87391720638255919839163123995833925713309804118637056913287576423800687260118169384023155637168842155964482385490838202095264873⟩ := by
  decide +kernel

theorem box_11_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      51692865319932297889820340213063569363159298906050441741857350995800337192691057563884050056915741223676059311940182162⟩ := by
  decide +kernel

theorem box_11_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      68556139727539810923205633729014692501288060408037456841138290221499412308403842849791555695174357208910452601⟩ := by
  decide +kernel

theorem box_11_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      2062528942972687324606943918106856645935485616542128526769445761723059841903445443462597022259⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
