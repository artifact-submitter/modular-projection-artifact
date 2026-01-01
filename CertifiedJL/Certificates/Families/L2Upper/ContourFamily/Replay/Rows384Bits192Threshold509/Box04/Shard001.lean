/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      59819161783597478436250710741789352747509688228213021187718037157435895890236164317035365258310350617333041081909991544712489414⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      31731728477401542726700313761245293321381152830923825883641595321500840027093550102094636536172881147401724476483492825⟩ := by
  decide +kernel

theorem box_04_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      35292564826632747283481800363771425395208948117582069891073290019355152774763448153020513815758692157231741536⟩ := by
  decide +kernel

theorem box_04_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 4 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      462583489193992524936300181240663945048611644301909426538810915969467437515650935013930390210⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
