/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      721630087843946470814337969738619281483767554718938572033400318228882027953745059455596048191314780667135628212161483256120716677434148565616601853995979⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      269152223468434400927735451493717220640649837856706867208847083464777610377422760789137839090589078735980801904584056156721641542886322351087485932839⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      13937968949507067789739354747571467307540969332518591746846792827011453836801014737774653919370297278793900097125510864324835914428311131476782⟩ := by
  decide +kernel

theorem box_04_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      13116706772615091364935048647119792951436854082412049908106163191578314276681871453940070178556086591294911173561434815154006746148103⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
