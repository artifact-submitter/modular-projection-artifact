/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 2 for box 14.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_14_segment_01_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨1, 50, 25⟩ =
      ⟨0,
      137267926543007752467211513928695077879947856645534137884459374667587627830213313264490233317226736385001⟩ := by
  decide +kernel

theorem box_14_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨2, 0, 20⟩ =
      ⟨0,
      52358797778180210950426911547999013297911759604440960777272876245327513832240555376678782383994197172638455904788859438106253405556870185447052328894522⟩ := by
  decide +kernel

theorem box_14_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨3, 0, 20⟩ =
      ⟨0,
      906062551341352805880062494892073470216993273142549705914893465944919046598082239122289791992948170240150569047487155243987468450437238980826967305076⟩ := by
  decide +kernel

theorem box_14_segment_04_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 14 default)
      ⟨4, 0, 20⟩ =
      ⟨0,
      41616703258691797357147575472089576915323521983712659431506439414312228563363649715551530597961921009080557134634263199927573969455830705067303⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
