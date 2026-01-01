/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 16.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_16_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 16 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      718598478292683461438479857414677929119593920943499220167886219055010774388249480775451292808913443475320952479356478806634789594621920424453943234442705⟩ := by
  decide +kernel

theorem box_16_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 16 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      1602856411204950066909466197452290819834210739993344062232181827469281177808512238231556417841057⟩ := by
  decide +kernel

theorem box_16_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 16 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      58073982462236375282161926027333423808⟩ := by
  decide +kernel

theorem box_16_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 16 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      282911907781873825646339910728562192866301019211004307946784396145593699177257624101361387227999798872094858897553036036678566523729267143817130179039399⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
