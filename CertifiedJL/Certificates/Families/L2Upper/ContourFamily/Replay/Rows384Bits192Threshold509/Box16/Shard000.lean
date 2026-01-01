/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 16.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_16_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      41212748006174118090264794896300814953240683601510814233332688155778863569241233031450716827796986316241058514691640867030691134000240762215470396366460⟩ := by
  decide +kernel

theorem box_16_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      14069724581687610328410058551254037974700878932351694190144107187544006734539707714589029837320595406209654232419087234062786352504335412834352787676663⟩ := by
  decide +kernel

theorem box_16_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4168761249845283583260836656431790984852993194647857782055346906052179115251029364580167528901360035590119552275010572034305536993690746128283441698⟩ := by
  decide +kernel

theorem box_16_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 16 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      6364471642056961151651596821456951766669083694759878702040589807488313255854920182582513678000152176425304164223535167164593513489646215303406⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
