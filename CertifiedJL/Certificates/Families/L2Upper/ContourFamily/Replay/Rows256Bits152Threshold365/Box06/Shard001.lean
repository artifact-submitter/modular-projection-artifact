/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      235840709529390967324300500837232771342479515662036499652905169414536000036683417588821771555381059360951502556638618345247801⟩ := by
  decide +kernel

theorem box_06_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      8711228806976149975716990602248526117606604426387423989853189610054585240252726993226016221504891899628400264164⟩ := by
  decide +kernel

theorem box_06_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      134581023037571238995876956016773841726989920673980384066377122570954469479994060467586692554949345929925764472430077176446423250106283455478937405191105⟩ := by
  decide +kernel

theorem box_06_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      10638961383017146984669817133574687464934978085482047288964292608948043538842034811989613182884682876569607979213021474114567376180148618918563246305238⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
