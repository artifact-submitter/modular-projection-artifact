/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      58753612025138567475966484436279508821424999240418242667903970375932025903578977289932337300843799658454834649921922483732912592⟩ := by
  decide +kernel

theorem box_05_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      30989924471194901194474896489688996168991297306843162636002559910928493256089157194152681468214828108612852208937793059⟩ := by
  decide +kernel

theorem box_05_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      34355646985205077857375262763218009752556774807125612113952425634932315817428832290132039049921405680448577381⟩ := by
  decide +kernel

theorem box_05_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 5 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      454605341210451680667973516339749227609546758594559291971851058406518805426049527879517310706⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
