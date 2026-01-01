/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      801306422723862372645618408088983512589418227851160003694669857778305307911604289507839597639460926108049652205872191384055644679335193288212901007957030⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      14227259895539483147649071473052418363235279734892281089548411580800927698150807279783456483997597522924358908805736197850670823308051996333187525451742⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3664399655591748868799630640267256362877777052544850838379102757522600868711592219763725682831632082869487546763322973619558427809695195304418663644⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      64161842444291453893552645647102321833770561376106826809491603788061442356190739059732165604106428748739393687511010892844269426892334878489781⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
