/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Kernel replay shard 0 for box 29.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_29_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 29 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      481465820651889147904246749140758797238348573732970344539257846873683627989417340501487674730166728085858220636650860589609063152184710558529403134276599⟩ := by
  decide +kernel

theorem box_29_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 29 default)
      ⟨1, 0, 10⟩ =
      ⟨0,
      10799118048953844913123131792017740289389307737818218299568716299528652449146046228940003899116060⟩ := by
  decide +kernel

theorem box_29_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 29 default)
      ⟨2, 0, 5⟩ =
      ⟨0,
      334311189835434333706873837337949784705709879850412326174499096693756601732585152442253105708642205818026775304474449904560155224260926219668⟩ := by
  decide +kernel

theorem box_29_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 29 default)
      ⟨3, 0, 3⟩ =
      ⟨0,
      136068307460829304629211193138967690244999478071201262797048973166782791352698814981746594985050975161235925354771443296403819349324113390603457979813859⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681
