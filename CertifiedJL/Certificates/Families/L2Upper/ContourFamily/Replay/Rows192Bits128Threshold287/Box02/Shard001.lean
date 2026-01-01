/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      427468640048748074509055523257163782268355069345162695517539891528047726440430029594506001394446716965169033058075785415802874607882404948⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      2620791617826400472195934861638873053468368926774321725626761327439033950684876580508022966024265348967707413013356527939454681316188⟩ := by
  decide +kernel

theorem box_02_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      33638699010122249352164934408017645509486645197659737530854744286638316361073707437809477276426870746435340913101144231429112641⟩ := by
  decide +kernel

theorem box_02_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      37400566849178318881145272561862426522845911919612024825736216281393370573898644505674944435617832684580316034391633511⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
