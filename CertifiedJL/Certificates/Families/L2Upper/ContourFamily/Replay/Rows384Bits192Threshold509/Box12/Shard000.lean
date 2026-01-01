/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 12.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_12_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      412260918704902070061815070693130214043968045396407446821659413067677666601734907969131842282185510767157417587255337447560843527679032360177223568362504⟩ := by
  decide +kernel

theorem box_12_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1426849879295502823767774559726114841928925881106965918391324100519920297323457760512625658849952667543799985125486043280431555612401048465886398408901⟩ := by
  decide +kernel

theorem box_12_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4468139053777719047011465242649122489552996448427104801930844777527882064470249116536295460863226321792882956671929946159601306285094702453431456⟩ := by
  decide +kernel

theorem box_12_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 12 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      83883995505895817983336569661675594263740331554031085199943167925579174816601179113976713314040382848805269726539868690926984672285626522⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
