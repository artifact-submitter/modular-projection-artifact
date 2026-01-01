/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Kernel replay shard 0 for box 6.

The shard may cross segment boundaries, while theorem names retain
segment-local identities. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

theorem box_06_segment_00_chunk_000 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨0, 0, 25⟩ =
      ⟨0,
      573747464514803100821481160596211522659970225198582529417411238636197682534788304325842210346470918475251407146883102048750930337659727738935553737486174⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_001 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨0, 25, 25⟩ =
      ⟨0,
      332019129006617463739415768719859752823083423979478667397117251891022991017576969633264517090644064324090618069851778164071700794700625938714551828681⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_002 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨0, 50, 25⟩ =
      ⟨0,
      39291848648868726446989198003317754878989489909845097725621655118413678462090844943396488396823842847946402868310019718091328800880734574273026⟩ := by
  decide +kernel

theorem box_06_segment_00_chunk_003 :
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes).getD 6 default)
      ⟨0, 75, 25⟩ =
      ⟨0,
      75147646884405808756983303432826854541597356344990910963957396290943098355090663216833213161678551778148487680515842477754953706024391⟩ := by
  decide +kernel


end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365
