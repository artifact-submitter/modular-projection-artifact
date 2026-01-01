/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 13.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_13_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      3785039888089642676112756055327606525242466152283844160065025110829242729204236609739921⟩ := by
  decide +kernel

theorem box_13_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      61323758915126231638158715336848475532069547358566737415835362369184967701388784665849922741452823444969214082784366124780916762576898061598377416523059⟩ := by
  decide +kernel

theorem box_13_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      4799036114075874334942240317700223823261125540797689025880418397199220739287673792051848919059006415934913160688319737246671996171041008745124317674614⟩ := by
  decide +kernel

theorem box_13_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      1482957583493034799525117292217000681564593062830330173872587261916408267487348460465243362536881711612356651324145259592813657226394421792397554⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
