/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 13.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_13_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 13 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      735359276559784655597852290585242883865030525791306752928219031449395503353865410784765247637510743297289536250782419130289611008845873606567765994716581⟩ := by
  decide +kernel

theorem box_13_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 13 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      987419448623979478140620268132857274096173898163816119963385232448032008014410283531127494185291⟩ := by
  decide +kernel

theorem box_13_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 13 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      19650306123392011083742045828818445894⟩ := by
  decide +kernel

theorem box_13_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 13 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      77368834361824773021281225565664541340763969182402731550244802225427287615605604383177761191409893172990552451764962385108364061342063640298342554932091⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
