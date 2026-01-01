/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 14.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_14_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      169958554572687665607585535202337156702501021584019778165383314559802930089614924973988285122100842330832036764448504717435713771207456750675195462854986⟩ := by
  decide +kernel

theorem box_14_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1502203764466018577931660149895195224439337730463062432655220726726662013419377159001586291508973887653189136141919795044526000310384029396999269627989⟩ := by
  decide +kernel

theorem box_14_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      18050939009409979451200450937771404989039847371177404921468166970508235697926892181661344003811489423991718452626571652917749164550126628598669834⟩ := by
  decide +kernel

theorem box_14_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      1237645351563629356944764386288935534721518072498168096482009971651276815702337839013536251733936632837628286696929420431282145848560502660⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
