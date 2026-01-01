/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 2 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      15073117245818411643593847362639301828572610544561869505801396151406005696396611900759123535240864893506806339581⟩ := by
  decide +kernel

theorem box_04_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      33076969463497300198726556630825229307020733468943571909851493722209339521208139114958430945632579402355379800996068350134277673850293773281307746166913⟩ := by
  decide +kernel

theorem box_04_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      81212062477820500842582982024840751541418560277872679924007970526866294188845536476322099779473318889733953251975656100480587880420465990686548246187121⟩ := by
  decide +kernel

theorem box_04_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 4 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      6329738851689368265167457184027176315076170714074521743452571100610479179196225938002935958743672207149173006796351235874665153837092427812220098958⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
