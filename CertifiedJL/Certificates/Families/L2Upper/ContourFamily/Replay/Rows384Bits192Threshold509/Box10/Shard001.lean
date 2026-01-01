/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 10.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_10_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      70813685851072060481599172135111424616639299592826214196221353073658645901255898276979052741680162090022957851265577431022500765⟩ := by
  decide +kernel

theorem box_10_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      39174003533625681100131597739058149399733501233908001690722946115823779065708341797757270664081278241819246063541039776⟩ := by
  decide +kernel

theorem box_10_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      46717630234709820936744008728076638553935574165595025254111875761287283214313097556156064112799891645397709074⟩ := by
  decide +kernel

theorem box_10_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 10 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      879788126589426591659818172633556579891939717596194357977569481730806155796250047048355140482⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
