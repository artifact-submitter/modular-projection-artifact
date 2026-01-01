/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Kernel replay shard 1 for box 13.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_13_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      767698670848262229598408413271704483174823473633168811411088028878588980476369138570511359544483861409781590550547966541825634140⟩ := by
  decide +kernel

theorem box_13_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      959975036061323172637474807611155698045935230381503686215980962410486644638312762933495619508200126540125106892796487476⟩ := by
  decide +kernel

theorem box_13_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      3838531197294799293555652072662740575396559422041189172084524651162546197706534678011714291818597596737836929789⟩ := by
  decide +kernel

theorem box_13_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 13 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      8729356179359269590056907554788161982124563621653853354685932910325938178996835463441830755800456⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509
