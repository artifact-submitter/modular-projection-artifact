/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      159376415570254010411364389673763842269741365678633889765205561881960743989620153406696534149150858078652231857901⟩ := by
  decide +kernel

theorem box_05_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      78636017049159270947143737065187348717403746841969722751722606940188064505331133062501506087620052167217749510514243470417058490351769229201970767303646⟩ := by
  decide +kernel

theorem box_05_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      39072286988820633620017937765295521498875226980525526074421079326554697915982692092479601508619357549662142425555938166507767037075971125196954459193074⟩ := by
  decide +kernel

theorem box_05_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 5 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      783198179777581753275378148240189373729587734348995306927943631463998486973657727779668130825511029113225181284994138965660191514584265366094784232⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
