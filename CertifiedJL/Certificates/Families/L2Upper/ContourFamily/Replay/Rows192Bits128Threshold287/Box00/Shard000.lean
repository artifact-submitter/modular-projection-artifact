/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      868463759924455773907517157912566227893922895757802641720367637072858442780389562917401827816557762069309849756152935318429135520160663233099141004650762⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      14915968781079177429435585930861422560796164319626004864522455798398999246278065066210369163447420443585661860793381624710089843946963112219668338699650⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3594473854107308577241113762390473606844842639841514709340552712082183359692762680054221802101009303183186473719627741461680798890737055432818796644⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      60325811248469236681257577766587229695319282651049483330700923703988609795448223310733042309785740856554236366310281720972557689052352092934532⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
