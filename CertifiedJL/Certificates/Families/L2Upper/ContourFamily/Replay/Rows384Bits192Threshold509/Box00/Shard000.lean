/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 0 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      763663154102757400243760186672790676725696127163556859761592440168877964372864338508729718405319188745218990633328949002625741256861195900278825256533182⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      2137199071874066725423096850488640377438522159607081324040117836328727557556162127446646425235118266401044306266731194119356323070237065553827642747994⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      4443325911190603932862667481380971143926774026625941659572154826136716779346348677094268868628805428971362759761434076302528169043386670064140113⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 0 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      57613368367133439323247808281061739515343140899022202700391309986240197010376624610951641379211840649648409997487505590873146490436600031⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
