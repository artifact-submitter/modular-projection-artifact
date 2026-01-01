/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 9 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      752813519802530722144155058243487838377938989382624743920186783760160702191282862505356522166076405164202451381160363003390792666072664282884240365595519⟩ := by
  decide +kernel

theorem box_09_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 9 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1490845272420585241035199703613310302468468274446517904570737927919003188855332511370310958155862⟩ := by
  decide +kernel

theorem box_09_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 9 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      25429986930275215996575219695882868671⟩ := by
  decide +kernel

theorem box_09_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 9 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      152680193652891054688043090663930397114361019438245503668900328882018643519351717500190984564734305141349355049638476723124915439146568857251033323701397⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
