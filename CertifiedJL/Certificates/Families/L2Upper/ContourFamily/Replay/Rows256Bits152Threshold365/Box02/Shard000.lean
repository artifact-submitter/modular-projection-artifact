/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      821704814851856321933198835150749571898565222984555203424965058567031428921140977561799675602808833397805465573511974511993124339830589053779762393261517⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      280527253168857514871325548016139981085291130072054861869239219746623811694496435049834282176774179404138857862595045693110867730441202489461942660750⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      12172277356883845310724588246641660746660444372825743216613326823005991317707111750588286948323975041223383768448272565116813423862866885480579⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 2 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      10382631960042880718843987812089956293237436869025034977930428746027718809765292323749389227801632247430687620967270052640864364637993⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
