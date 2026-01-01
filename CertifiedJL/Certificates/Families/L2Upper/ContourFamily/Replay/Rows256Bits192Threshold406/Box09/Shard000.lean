/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      34967328864619776894390160420003032222692564796987924147850675049649844749650379134737034089729501894426484592596795762060239124711609761285732597850876⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      19018248921047244068347377688100625587692356760491643642873218158982463301957104136294918095492866138925183218568443584572934004460792900352146557872824⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      1093383821148570103873189666696737726303545056156635411727423310950953640417095894343920582616275769558145505730994737086513419035493515269209862917⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      633941042005885367405553584127202747315447430437982904070682042628717102674937916107181184610956888929827039192447333486671088409300343180873⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
