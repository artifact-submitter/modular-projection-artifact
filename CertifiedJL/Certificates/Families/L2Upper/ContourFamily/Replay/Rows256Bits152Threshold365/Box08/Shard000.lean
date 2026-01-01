/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 8.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_08_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      263945987713493165374745622459706755233445506125894976064036357873319889709469888562281700775245772333547814488193716930684852502799061377319077116889986⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      784863651524130195401423759417634894255726625932210432057169429433972343285634363059159323690839631579778210851072067893341338383555247660410729209470⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      372561243784958079602553836549264133435109657253700874290469061409559302832838286403417827678086116659059894119822399563147317564740611578056158⟩ := by
  decide +kernel

theorem box_08_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 8 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      3282417124036985930938802811653527950159043833265213432167185862627841983511326077947845335645281834291860531437561039085128067280784029⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
