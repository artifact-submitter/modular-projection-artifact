/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      36690114244803975670743392188474293583454923935013427835838717919485465434371858739955851296903405622590186072837704527759079540975120214133⟩ := by
  decide +kernel

theorem box_07_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      974268156432673434198265808276278027953647456864333049808307886759675784548184222517703097620116379148224716953585856301349607238676368⟩ := by
  decide +kernel

theorem box_07_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      116035377593134099451165912021009686820873501515576415327237686897649062502320969174103880322709160964933856156110622448902304608520⟩ := by
  decide +kernel

theorem box_07_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 7 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      1658665205304031176761508390230064669172388889270095450315643619325486630509941222800844362609420428052940391923410644711856821⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
