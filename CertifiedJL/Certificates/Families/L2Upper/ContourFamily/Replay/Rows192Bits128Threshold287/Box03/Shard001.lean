/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      481092123612894142439339456969569098994435776057031718812374859628586411317647230464791535026922232411700719978743283167111061343264900430⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      3034566688383794454354865156321792631297471222682315132356430167376352988824233297821369532695274138340695504569354350040346203162812⟩ := by
  decide +kernel

theorem box_03_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      40550666128262088549423169178963038128515517756536407722064861190461476804150727271853917627023264661573832124223927645986157956⟩ := by
  decide +kernel

theorem box_03_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      53014147897277620676234911828808603213002931126669756446131332308057422417073741338690211571979004370609346308964800433⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
