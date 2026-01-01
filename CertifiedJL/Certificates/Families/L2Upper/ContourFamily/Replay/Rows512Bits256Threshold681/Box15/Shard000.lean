/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 15.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_15_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 15 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      725254499598437258999764045961713643046641938861661745715162029072351657616673857042080185473650882231363366972904999047760051116884388702790746670075872⟩ := by
  decide +kernel

theorem box_15_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 15 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1575404736009883650677827831168385976106930901346986949028344521000871749871629781908179741713900⟩ := by
  decide +kernel

theorem box_15_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 15 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      48637331827451707564364156231954110146⟩ := by
  decide +kernel

theorem box_15_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 15 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      63669561136398029332571415478489879130620865712304936223101240470404374075710161622620840173424139736860448729142542358640170750832512519997600609268135⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
