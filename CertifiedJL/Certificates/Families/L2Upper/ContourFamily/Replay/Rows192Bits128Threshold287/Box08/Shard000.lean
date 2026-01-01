/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      251322703610262593883967946695109917119549734680350333916989184879668357558715437504706915174739991262612305104794500903515618142703147121068328573039075⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      40027001752353194236701770328115413364068766712313510193463377148144081087643886253506071436363542470314404966695963604301228917439357805319063294440954⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      83004383474582039818552390999874227946782447136105447026273488384887903141629555828785215895870747761903738289001652260458440854294425226127622511546⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 8 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      10880271482826550889561347015301707399022288832800237543727452131485098556614473269063121278869892413147832487086687566088960387586558410646797828⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
