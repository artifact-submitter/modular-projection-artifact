/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      2302561985302821136520743498029131429448205428550071485958756315057420545916331894338353439122106427711825973317⟩ := by
  decide +kernel

theorem box_03_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      224123042314728508616210419359986447817524952700778451467121831708693357326019512407422607207589458853629337877767643374909290172442⟩ := by
  decide +kernel

theorem box_03_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      135838801089597932333306720692896706120314067954264407006113668235267306630816210207410963087343220751571536465709550918472671731412746814989247494132027⟩ := by
  decide +kernel

theorem box_03_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 3 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      79220250739676542117698214936007291527427675330040620321095900493614576951447802957224519716717418402213883185598940857621116269799014518583432487366⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
