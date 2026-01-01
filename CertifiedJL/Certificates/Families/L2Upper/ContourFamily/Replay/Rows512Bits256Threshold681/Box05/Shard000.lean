/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 5 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      781926357397856686675251639179117199759418452974473710946555213196487866735904652930747620223515224036837162220117024226731218930318468583364020672762719⟩ := by
  decide +kernel

theorem box_05_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 5 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1414245355583473644126540854875872152176193819985367104482302167096081548941405812768423897904877⟩ := by
  decide +kernel

theorem box_05_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 5 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      15874571852983229064795999837882246214⟩ := by
  decide +kernel

theorem box_05_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 5 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      8199199931611429540798415574970942502769711782371892688156085964861584735594645811565042822134796601961170729506366860074964972567529454329⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
