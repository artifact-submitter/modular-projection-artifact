/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 24.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_24_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      669815001652766362452939819122525947268097554972118344887921444393861706527522503600204942869088663210956192630021425101915982403987490887404413656514599⟩ := by
  decide +kernel

theorem box_24_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      4506696247447774041238706874164784240698538962852480392549177783197969614912338371789965138138356⟩ := by
  decide +kernel

theorem box_24_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      1303458431402856401092839737518943821822⟩ := by
  decide +kernel

theorem box_24_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      173388050782157126503669141529251914106459984742577637794433175850123998291740148034741228991738888445003661958569623377487726635355189563352828137848835⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
