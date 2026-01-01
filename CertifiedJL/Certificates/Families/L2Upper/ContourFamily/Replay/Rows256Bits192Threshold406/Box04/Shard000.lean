/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      463499438470815238624493676183793464717850793999296318858812693012178525842833182940172921507971103714849709872214623722016975961702453843824778761941217⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      13748471160451721627185609835943774417617301857144505926269320335382013225130240276948817679354502339751069334625671198288198916088492341160422087177⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4589327858475422111953342520258208769213106600493934721995330287402906271644577707374783071368357180748184872086467789444604991601445177989⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 4 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      50956541351569316874874977534659948609668281120385696169861598672381943949615381412163319835753934925193068126363689090176180742⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
