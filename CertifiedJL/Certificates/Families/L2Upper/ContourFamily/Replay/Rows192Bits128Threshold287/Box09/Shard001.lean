/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      767562894158020182246987706246334311693965552481136642204058656888244422807775547433789874578633131992685431590853715346214231558689417770368543⟩ := by
  decide +kernel

theorem box_09_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      867186948553023858773730193024821644912968454775869515870814970455089490977185797100588112600642316903861928266665297737350210942318272070166⟩ := by
  decide +kernel

theorem box_09_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      2681064257914388431384740086099632722309945999607208870957470839954364783146248412317158989799674295480412578077290162937045723287555568284946⟩ := by
  decide +kernel

theorem box_09_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 9 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      21231644509426436838463258885368638266307363568624578511087209220134412808705475589291829046415016306000753974247034480866204023835242924569091675801599⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
