/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      632403757913227950531935215174222327444871219644546677544949574983894998292652669490278859428566406684926814494940248283644464744645845452⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      4291493022097332535612177005829155474212961848915455635775903643123761174516657869362422431542450857364516125907316195457095743286521⟩ := by
  decide +kernel

theorem box_04_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      63773278871851320971287842353786451286056317266012842853767009857951413823120874543958639066469270839230231168193092250579689365⟩ := by
  decide +kernel

theorem box_04_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      127030199066174565921863874899896312893848399235320872972603040651428834022904063825827414455956704306765273752900896757⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
