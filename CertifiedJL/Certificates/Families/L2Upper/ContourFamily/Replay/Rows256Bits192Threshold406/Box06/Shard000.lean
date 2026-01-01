/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      324147709070824856668761496663206163334463473207928726460175787513177263173494532742374821748643060859305532424168386224347099995897632911961268939871632⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      33203278008583872093953062800787533221739351706545182337381650174619755645034016528388005252441233872984047782332525686721943950392967322792838762571⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      48927225555609585014948912276576165197902372607840219123358504991423704320871756337443761020103246004778795992142247532546300722668608671023⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 6 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      2025637478450692059364186749473640394733316133766794209217486067179417440147510038221820750265443854006112104235560447804908700204⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
