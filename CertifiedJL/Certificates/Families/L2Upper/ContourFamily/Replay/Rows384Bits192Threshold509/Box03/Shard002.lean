/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 3.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_03_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      660657679066773549032892088473640222942168733627641220244538687064720946979566⟩ := by
  decide +kernel

theorem box_03_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      436903330131686428403537245500163253171968801358166210031484661026⟩ := by
  decide +kernel

theorem box_03_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      43596134673597504126455187975669807632306965946660099949357054939728160402031405723348148999026286805295589411726844847469815123062683765813669577455282⟩ := by
  decide +kernel

theorem box_03_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 3 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      13294886118982822854653460845214347849682705221749445736339107160382922489707084590220813517319627242391238580167296072814405837241293484494771762569611⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
