/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 18.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_18_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      705545448322968699127870784957094791723255202789967359462158759927209290067864538246863491346039314693126754218947041416247079954690641438422454275111287⟩ := by
  decide +kernel

theorem box_18_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1660644847470906370476387148108876344762166573031836739492745546272883037260649502172008405689985⟩ := by
  decide +kernel

theorem box_18_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      84221729559160819343326590889602247849⟩ := by
  decide +kernel

theorem box_18_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      336689835095815196248187512243932117837276728145823680066150521643535026565621737579748804846195664863924798753851649694224057638625892031150323476021349⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
