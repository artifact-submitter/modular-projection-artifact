/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 4.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_04_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      14814197093267107212790824651528882739155955229984330084518481183683167127345888180748157842254559669382552990272170276484010⟩ := by
  decide +kernel

theorem box_04_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      1897348882362511459835927061915523362314049455371196808628726025485935507348547202739833614521990928620320104⟩ := by
  decide +kernel

theorem box_04_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      9294933831204528852270506695910376711819559306282906565566891629076727070870717081346673344610602982413734089056886221347635791487999489453888855⟩ := by
  decide +kernel

theorem box_04_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 4 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      99038714226835140914477370588088476799770301234731585606123619482950318321445258206122460896911741917444395472083185917775028653590029746593049270905088⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
