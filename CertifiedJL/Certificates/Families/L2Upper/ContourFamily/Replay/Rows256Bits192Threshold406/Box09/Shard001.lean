/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 1 for box 9.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_09_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      8257335392689336938395159949005384406357567264769976417950339170808407866165094627243004363430882319943317948260382765347535417372471875880778852154823⟩ := by
  decide +kernel

theorem box_09_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      20094114895300342597389173885925540051813027239956069999024672452237888493470987283457667627212847246347765884686848575993827879224290471058752458140618⟩ := by
  decide +kernel

theorem box_09_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      19606919755343018914885330923318134894805096502911329826423652109409896436029642664162986617041807492868189565093714329191902722934101315237940587905955⟩ := by
  decide +kernel

theorem box_09_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 9 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      417828821960386565405997968202171170228271483917154607691436670418377827540039456326214320578943808054063001675684254207694298946656850829030590092540⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
