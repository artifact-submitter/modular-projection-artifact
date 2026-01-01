/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 6 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      774490127547579443289887722278344696204844015961380694828004949502748626109464685057283779191861840133794179118748977326131245922114964444794693761482556⟩ := by
  decide +kernel

theorem box_06_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 6 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1435059068501471861679205544752270529680069353826013251051834234878918548095499329953765500965543⟩ := by
  decide +kernel

theorem box_06_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 6 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      18003390038483713116904001129436023658⟩ := by
  decide +kernel

theorem box_06_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 6 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      157517041020336195753550976975105128552463581213853025641518482994817242105019342764335604384806275373771755744906217734600485249961572433920934736499446⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
