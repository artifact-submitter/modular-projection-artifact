/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      354316173097639722046754043863423609050889051960234903535297728281519468746485739254198024226886211452381571617873149140673874106452452074⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      2096879877739815110422752620335761385274430723083656250756159058465333189968147423275672375290669677505016989873183884733988488616234⟩ := by
  decide +kernel

theorem box_00_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      25665982073084070565622853411564293096310498008527386120723362216359228515166900686872972549007442129651768197004747639850494461⟩ := by
  decide +kernel

theorem box_00_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 0 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      23312498082001336623504242263512885838345498430016324601422284225591989128191918074274276834081460771812993912767002786⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
