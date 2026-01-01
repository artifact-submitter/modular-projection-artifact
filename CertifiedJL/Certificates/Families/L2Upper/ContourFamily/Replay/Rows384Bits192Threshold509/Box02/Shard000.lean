/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      719481933898210685736797309348795098847148160342187483965164596778518330074541369796969993246225635659960885392444857205725193950638848437122850566755245⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      2040629131574960852918360194705969773072634617017315581609385964953796707301136861387814613559455544396835581040241462664080176488849045668721350504909⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4339532897814537988146272387919721463027669521225275928292771902781222345233090348045787228521754953925246624443221861457993442028196505568619616⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      57209394348367460101818689393265016952415255246558735578822898453045460632999004183257487537949121523513164888849671922852761261943908357⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
