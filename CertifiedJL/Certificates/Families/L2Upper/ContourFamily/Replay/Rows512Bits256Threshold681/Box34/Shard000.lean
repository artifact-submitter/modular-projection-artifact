/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 34.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_34_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 34 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      29981863203412555084369618571513128503717389466128474869706312157513175919104315254284779597620012431049004849941482718733515707803502061228529145316117⟩ := by
  decide +kernel

theorem box_34_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 34 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      6651793734936198311059068523263952836947287322548548277288518398594721665028045441351130870478700149653134460323969063521930621784814316279636212993739⟩ := by
  decide +kernel

theorem box_34_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 34 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      10954479545926302400173631431825028337729345669993647940705360221820689810075412744931226214900344641088608896957590645585809465597930733119118208733995⟩ := by
  decide +kernel

theorem box_34_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 34 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      160901122626319429157043934826304835833667559657651901339025794409404685740133578366277549824567453393272787081118470205817624100686392510652894654472⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
