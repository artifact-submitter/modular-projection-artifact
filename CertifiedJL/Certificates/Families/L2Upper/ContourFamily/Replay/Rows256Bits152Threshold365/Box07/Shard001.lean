/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 1 for box 7.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_07_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      3997457350466280937976243990983831468216644813997784555317470438158462943139598573264589096281567633519798346263378666571760988⟩ := by
  decide +kernel

theorem box_07_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      971482356446520096540457618088212556057311763253243006618825792640729198953379226068610258693627185980322318260637151537⟩ := by
  decide +kernel

theorem box_07_segment_02_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨2, 0, 10⟩ =
      ⟨0,
      122214250355756755593282061477055641472553700188268650207560609438757703487918523056140058565544402756691708113837751968455955547614905142441533481844863⟩ := by
  decide +kernel

theorem box_07_segment_03_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 7 default)
      ⟨3, 0, 10⟩ =
      ⟨0,
      2799970497643402741584205986921512009001855360025782792684932651070141773298328670067714729788480731296369447914280387733454584075761209471375141508498⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
