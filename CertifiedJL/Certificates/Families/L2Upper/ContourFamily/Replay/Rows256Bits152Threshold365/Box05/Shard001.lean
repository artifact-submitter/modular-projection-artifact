/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 5.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_05_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      19716526529482898606678029176970511639156123831487189137387588938053807088669852865604075828166708816802124937303513277147446⟩ := by
  decide +kernel

theorem box_05_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      5655368844365591369043588521155000105845590094902799514112151881318581455546040093324458053234532789345710511⟩ := by
  decide +kernel

theorem box_05_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      48856512841798730349955011463371622211189296630710106255405803903730693191763844125705249118726309506578779634949587375431289512082530060178825533002042⟩ := by
  decide +kernel

theorem box_05_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 5 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      48984314570448792258771337214586479840760814038129249247332454731535691200229076092696682638863409286295246680431607989150481324161372244160755337654648⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
