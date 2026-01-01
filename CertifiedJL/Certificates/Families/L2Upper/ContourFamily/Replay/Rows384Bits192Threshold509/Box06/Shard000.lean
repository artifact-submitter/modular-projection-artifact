/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      643808732138353411605893782446292305445785571213815840759320365754482988570773998039796682104780050373041524687223500935924632325176762136280904508542724⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      1876261479669942099632478149695120734667810050540562798646369297552436782820589957964284968524760247003098159576097831649757433385683542647007558813616⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4174488594811589858370663483510996665806223941912332791214592856641389030827409765098775924641814203259497135509541209856765394136834326873128608⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 6 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      56566442495566113434077243144767309718186690236962734224048200323718258072507263506949865595323764352592746234292986941126070242242463478⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
