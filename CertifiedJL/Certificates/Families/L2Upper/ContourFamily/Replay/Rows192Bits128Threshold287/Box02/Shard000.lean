/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Kernel replay shard 0 for box 2.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_02_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      745928974519551257662014343458989477226604836119698366925728029346910701238975561486283273094343336770059820057348699560205121964056506611822625861440584⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      13728611087160166815381791162618927171157813807867816781515714578675223993275216714516373454041358024352628115870297535196099135308016216162862248428785⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      3773015086114201200566916685454841283947182404472733298951606412162487269771670301175987212015448275651601566408203864394883189775478211704967087000⟩ := by
  decide +kernel

theorem box_02_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes).getD 2 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      69157306789646353056171653822223933881693733513441724489120662695323264864243268916370800908092361985939904166383789354148000629075105150657290⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287
