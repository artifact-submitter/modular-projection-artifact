/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      1256397519466488815995294899158830691416018836117502184192901655525229916710199900691362706881472153242291286287073526⟩ := by
  decide +kernel

theorem box_00_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      1872478604816175869791103633120713083440686274816127266063126538587826658401847783927264871359252806⟩ := by
  decide +kernel

theorem box_00_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      180359999624865342845553059943789157269200154266437877091843008896690680092616465678861⟩ := by
  decide +kernel

theorem box_00_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      89419034855393533283439288065246465678446495308339665506473886660311932158775198287469504853453331772664868238065798296288085164310100752880759043109575⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
