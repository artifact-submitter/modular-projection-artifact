/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 1 for box 1.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_01_segment_00_chunk_004 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨0, 100, 25⟩ =
      ⟨0,
      385542653595737049277850213733814209336520093481324620171522113725981681326025798140182582626078391839508226790277934597429540628995170007⟩ := by
  decide +kernel

theorem box_01_segment_00_chunk_005 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨0, 125, 25⟩ =
      ⟨0,
      2312707135690642280888733425874177257950573487344500092391797184381456043358563521668985939755805020872877563966875811912854210681770⟩ := by
  decide +kernel

theorem box_01_segment_01_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨1, 0, 25⟩ =
      ⟨0,
      28804959480970372534222237404910480333751994306613182495184288065407705211422922125351961964581745373866359694972935829542033730⟩ := by
  decide +kernel

theorem box_01_segment_01_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 1 default)
      ⟨1, 25, 25⟩ =
      ⟨0,
      28289177042244711201121902707428704380950580312331446919163746711043654828980797268277934043493265153896810231379331182⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
