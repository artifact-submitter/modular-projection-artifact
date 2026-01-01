/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      882365896341111533282512722426695784426845077256105358880134215180313658961993166016389416452646396587440079771396625111594543562047429422230790815617375⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      293099666090351048756009147716973066100118366403392511855480229382074705815011859710806196548808658422678373900548292382393612177359466732955681490031⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      12379155255890521245510035107461543224773154371069553024475227269848727666886770843809995852957823029247051050806553029921970857564135067303133⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 1 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      10619530695359530791161896800516180302230521152575723205743385498392807406501210552863328273576580282721918655836499867057111809716948⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
