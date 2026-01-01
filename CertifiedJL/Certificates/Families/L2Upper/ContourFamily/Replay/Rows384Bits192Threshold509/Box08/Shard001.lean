/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      63253070132867010433304617558838416498447387445962367177503221609680219073160126698384943762512012610244093322594166929530960174⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      33847734461584510385551835509408788879183379051166515012142598323636093306257274380682433510633587681270894414827787013⟩ := by
  decide +kernel

theorem box_08_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      38259790118663918999543813621418902787844144015572319620269039946948326319552419920318050163321650026839738355⟩ := by
  decide +kernel

theorem box_08_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 8 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      559775861454750802370352467399286817986344532919115241711934028291294628648120080740975146063⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
