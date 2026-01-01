/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 19.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_19_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 19 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      699144780749181569278748761608718196671806392760601775663267283588382891619922535672924254368346065682683432870784322509153457000743853007126492448181581⟩ := by
  decide +kernel

theorem box_19_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 19 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1691028485961409920125633548485976697474053547844356601098706251267166608637001601279440283245568⟩ := by
  decide +kernel

theorem box_19_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 19 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      102272687726981192753755174855343678364⟩ := by
  decide +kernel

theorem box_19_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 19 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      333262168787464660186313607573496812801705581773639600055981577115093350569973613707172581179051067334355994168396249165271759082754351438426656751354055⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
