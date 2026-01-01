/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      620778650917898745153344271400141754485687386330660181047702267879507371472484⟩ := by
  decide +kernel

theorem box_01_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      320571764918348841900122532380129094528651971476007614581365311699⟩ := by
  decide +kernel

theorem box_01_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      8949791792945491677494454736204723434280915587563585498095452858072803379129787874956076922986608406413611780830849⟩ := by
  decide +kernel

theorem box_01_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 1 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      47903168509915642886893868131840349179089073004901441775888233526032832313534724728720235032219355131185965367657095516791142395040097054446287345310902⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
