/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      179898274631946862770196902575626327442485602362745327404226813250404294799707173189683736990628358316378508898082597178525019626828878930379290344975988⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      109770112949484215783075547781529093863247428016148000068701149700230610928226377390592581768393670102899843501307513883658810874408321227156506473298⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      543724021927818058767008758041796948760832376015990139235918816729091897513592632722490102843535508670243781452419015185152625753419365744978⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 7 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      90098567856375109063046879294829865313852353114366654678818022543612470333176173551750680041778029203641280405910752072892511883081⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
