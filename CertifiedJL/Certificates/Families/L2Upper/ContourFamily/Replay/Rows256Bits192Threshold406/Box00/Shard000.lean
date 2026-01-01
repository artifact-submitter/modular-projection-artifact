/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      729379268250022695970531275050713124855112983546764938950976706094593299714684105596368443374156387831139175889118479483516552521327015562651757843496164⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      14342694341191362540398380123464101727050709623892847714933619977736230369854991857174140218313137423278549149494176778265164410633190114442963720346⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3068012472820130038646963533895021830526803043378112400002694766058715063277190767067684648170590925038172693704760647436453626374727095738⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 0 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      27835723380755321585388143069051896736815528096914645985011842745201967356843254154875096305755342951910309432951449710169896707⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
