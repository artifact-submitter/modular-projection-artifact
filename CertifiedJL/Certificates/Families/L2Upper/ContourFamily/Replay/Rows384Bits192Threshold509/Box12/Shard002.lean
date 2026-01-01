/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 12.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_12_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      375846929837197279191382587549018070042457588847860157086096406560426095113630608⟩ := by
  decide +kernel

theorem box_12_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      20894133316619515272380403516429641655886695137425242068475108185018514953748431812874691908735166283484642842120309363400244800689935959666867901621398⟩ := by
  decide +kernel

theorem box_12_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      26716681931116875002296417595696367194843039590706227223765021877885585066861140098725219283177494584951708583140262139761733732972120133008520890770533⟩ := by
  decide +kernel

theorem box_12_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      347576366140218302348693543421338381631816619332073739594854544046562358805961444109139321191961295519260606231660947278126338879946283548036121811⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
