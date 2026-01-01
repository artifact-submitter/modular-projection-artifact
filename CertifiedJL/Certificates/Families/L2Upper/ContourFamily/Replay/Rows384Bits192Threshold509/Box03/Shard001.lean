/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      59625444082424467732252860469153640718440118522214190337363300429040445039787890866738731412016093010208131242579678068418625330⟩ := by
  decide +kernel

theorem box_03_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      31653457648873451893225436464370065606340455669311242376351233815267915704962153997927042669148376119774722774776433897⟩ := by
  decide +kernel

theorem box_03_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      35205237954980518396367510323273824532926262427053621369022026690986940990526635787481796858151021861897537576⟩ := by
  decide +kernel

theorem box_03_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      456203068737583235562034185629238961884352964025675790231672779961178331258291381434772105757⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
