/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 11.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_11_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      28778054788306339882106069996790526858649688294224469678421553784438380806570247⟩ := by
  decide +kernel

theorem box_11_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      545173606459432794440033882656598654124866973249590400333775178243022821463192570605990171842556942173727864159152694254662090471173064268347⟩ := by
  decide +kernel

theorem box_11_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      58035526975595711909084576048677473865295513790762594863541095605654741661343946601431210053046905327186484231970728579537448646121522547235939726151783⟩ := by
  decide +kernel

theorem box_11_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 11 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      2774753991860762892013133436974447470075823884738614223659733698001109037022913743782563073756378034064477175622202700952436316873505189038382502321⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
