/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      59911162068122485857693012582388545276468263244518430741529408331067436885356273884214302581603793910727184226470879509376557089⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      32096753173227155470696741439356610803810880805950487823458631008230405503690875537590296377602849593066221612865268365⟩ := by
  decide +kernel

theorem box_00_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      36053754100974998265880600247929189817164203499799256112501315405215645049193399581368409003463050090730053335⟩ := by
  decide +kernel

theorem box_00_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      467117375243420417330725879171501506491948366229210986913831208936065188951648415430472448142⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
