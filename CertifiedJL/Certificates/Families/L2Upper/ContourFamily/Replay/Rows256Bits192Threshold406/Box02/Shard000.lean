/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Kernel replay shard 0 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      570906899428353116306669232433777920223394311538335910156393150260147336431450194807492997770830807077670993811844553757797139195970246055364946908499497⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      12972090377855233178345673282507354936884335567649001259436821332431278895211393665059927641196777559557223234136689509147109991184457868664360729805⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3138782945077911881165389185554753818941322189701409234519646133085954561715840532942741023220496206989819858792878094321033549878516990815⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes).getD 2 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      28569955638194532557163298370070028660245445870960735509645527759453755187269296554321541804795812420278442579814305672973248108⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406
