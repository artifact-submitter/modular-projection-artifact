/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 0.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_00_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      951715309164456360245739403128423115283340659518330381269898762213746595924874062854851506228565185324879730327702407110490931506251197088858096501510228⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      305494846221894546469795886604488693453466754615658493747453814130527967557353879116910417450149929789797939425938289802895260884086769991271215027520⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      12320372696463131080293721253298936219394560455020370066537832508781644550809228809039044101348790788433452042174292951859577757073459550571912⟩ := by
  decide +kernel

theorem box_00_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 0 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      10506483273537744765539841897712677734480543756598687103050364230558481366297343070994393610624530542108906830284096236733356804042058⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
